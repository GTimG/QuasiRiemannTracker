/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission22_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(189620902752067113/786981005458153:ℝ),(187833921746608960/786981005458153:ℝ)]
]
theorem admission22_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission22_00_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission22_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_00_coefficients]
def admission22_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(138467137397287168/786981005458153:ℝ),(137467137397287168/786981005458153:ℝ)]
]
theorem admission22_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission22_01_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission22_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_01_coefficients]
def admission22_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(70422330896139254/786981005458153:ℝ),(69941200137369344/786981005458153:ℝ)]
]
theorem admission22_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission22_02_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission22_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_02_coefficients]
def admission22_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(53983129988618646590464/2360943016374459:ℝ),(321705951649479884536832/7082829049123377:ℝ),(159759405683623944765440/7082829049123377:ℝ)],
  ![(53800031247749163634432/2360943016374459:ℝ),(320607832000026411216128/7082829049123377:ℝ),(159210591256778920312832/7082829049123377:ℝ)]
]
theorem admission22_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (9717443314012385273/19340845190139568128:ℝ) admission22_03_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission22_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_03_coefficients]
def admission22_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2892797315893629262760/786981005458153:ℝ),(5721626941730173197312/786981005458153:ℝ),(2828981663156315226112/786981005458153:ℝ)],
  ![(2910904211396951871902/786981005458153:ℝ),(5757638303337903588608/786981005458153:ℝ),(2846886610391481778176/786981005458153:ℝ)]
]
theorem admission22_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (64750251689673963/805868549589148672:ℝ) admission22_04_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission22_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_04_coefficients]
def admission22_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(605460410034306374783641/295117877046807375:ℝ),(6060379396756395498229034/1475589385234036875:ℝ),(1010980114120097484211943/491863128411345625:ℝ)],
  ![(2964753886513249612581707/1475589385234036875:ℝ),(5935687239492229559789882/1475589385234036875:ℝ),(3600964745693013432669/1788593194223075:ℝ)]
]
theorem admission22_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (2964753886513249612581707/66016751582343059210240000:ℝ) admission22_05_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission22_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_05_coefficients]
def admission22_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(282599767965690475283987625894685432401920/206239921282991172178485579079197:ℝ),(93055487433900241071008411201002342600704/22915546809221241353165064342133:ℝ),(827250823060826982534177746442204733505536/206239921282991172178485579079197:ℝ),(74351933653011076947111608934717194240/56303554813811403816130379219:ℝ)],
  ![(284213599914307922946175281881107116416000/206239921282991172178485579079197:ℝ),(2529490268329025221267067006224590490624/619339102951925441977434171409:ℝ),(832051181136733441768340343775141016829952/206239921282991172178485579079197:ℝ),(822656006972614552621727287037415915520/619339102951925441977434171409:ℝ)]
]
theorem admission22_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (13295161781253411223967959094295/115309680258685755015435016640512:ℝ) admission22_06_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission22_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_06_coefficients]
def admission22_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(168098777689320677128082976884810888/15355514949221291949853739787:ℝ),(121055497165769939140668899647045489664/5574051926567328977796907542681:ℝ),(60037597704542129864249702262930636800/5574051926567328977796907542681:ℝ)],
  ![(20181009424490999551271698849874990486/1858017308855776325932302514227:ℝ),(120105732999078479797110884073679294208/5574051926567328977796907542681:ℝ),(59564653827657334092890186008780636160/5574051926567328977796907542681:ℝ)]
]
theorem admission22_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1817768976674112978909002258568745/7610438897073259831018711098273792:ℝ) admission22_07_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission22_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_07_coefficients]
def admission22_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(1845538577808807864746217205120847070293071086203632248881/54434100845384072048797925221494140625000000000000:ℝ),(126508293743800345070391341837466491182256544125788289643/1209646685452979378862176116033203125000000000000:ℝ),(5849034210620391175897955981861298362318070413570783029613/54434100845384072048797925221494140625000000000000:ℝ),(2001696132836718280723282733540214048974532943801442244559/54434100845384072048797925221494140625000000000000:ℝ)],
  ![(4176215659722185377037786214394554221418275152321881903841/108868201690768144097595850442988281250000000000000:ℝ),(1425796744413060801415884301757399127863522575042129599989/12096466854529793788621761160332031250000000000000:ℝ),(6567768861492260400523079634242714461122643314797226248429/54434100845384072048797925221494140625000000000000:ℝ),(2239787893496147588791411793564503243604425156784209000399/54434100845384072048797925221494140625000000000000:ℝ)]
]
theorem admission22_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1845538577808807864746217205120847070293071086203632248881/623447154448241445357052813170589040640000000000000000000000:ℝ) admission22_08_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission22_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_08_coefficients]
def admission22_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(5349876211516553551464513212600553269371195732/54434100845384072048797925221494140625:ℝ),(15733652642081094588653392575008877295204037948/54434100845384072048797925221494140625:ℝ),(5139447335172848296399166707574001743506076672/18144700281794690682932641740498046875:ℝ),(201382737317578966378502262342591778703040512/2177364033815362881951917008859765625:ℝ)],
  ![(42013886641278391335196755078431345463040039/449868602027967537593371282822265625:ℝ),(14939692674835029499714689672352482885990964541/54434100845384072048797925221494140625:ℝ),(443302787920456093460386635729091936191249664/1649518207435880971175694703681640625:ℝ),(954596495432887012183892833002588574740717568/10886820169076814409759585044298828125:ℝ)]
]
theorem admission22_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (116527892508897340354479105591136300627529/15220877794146519662037422196547584000000000:ℝ) admission22_09_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission22_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_09_coefficients]
def admission22_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(247940355487259731990269651859456/13833650486569095703125:ℝ),(1209657378878911308118682351183872/23056084144281826171875:ℝ),(3538976126196153625632419089211392/69168252432845478515625:ℝ),(127745151532371484580857810550784/7685361381427275390625:ℝ)],
  ![(2409721737485162404298585640805376/69168252432845478515625:ℝ),(2349964361178115688929962427956224/23056084144281826171875:ℝ),(69402945356079643518874354397184/698669216493388671875:ℝ),(446144288314227509175451888451584/13833650486569095703125:ℝ)],
  ![(129975134414895407646490916043136/7685361381427275390625:ℝ),(1140064581661672573104660833345152/23056084144281826171875:ℝ),(666238459596412000581786971381248/13833650486569095703125:ℝ),(1080775363309890014913370601259008/69168252432845478515625:ℝ)]
]
theorem admission22_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (32982646585384827115276202431/16504187895585764802560000000000:ℝ) admission22_10_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission22_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_10_coefficients]
def admission22_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(413453291773277262245383754647748200/46066544847663875849561219361:ℝ),(99250822119752418887345232358432901120/5574051926567328977796907542681:ℝ),(49224846189891997617208357169284464640/5574051926567328977796907542681:ℝ)],
  ![(49626938770636573051943508017714103358/5574051926567328977796907542681:ℝ),(98452340906329209339397330873518573056/5574051926567328977796907542681:ℝ),(48827266505159800338731906719378751488/5574051926567328977796907542681:ℝ)]
]
theorem admission22_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2980179840402819844893304853477707/15220877794146519662037422196547584:ℝ) admission22_11_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission22_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_11_coefficients]
def admission22_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission22_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission22_12_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission22_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_12_coefficients]
def admission22_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission22_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission22_13_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission22_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_13_coefficients]
def admission22_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission22_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission22_14_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission22_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_14_coefficients]
theorem admission22_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission22_00_pos hδ hp
 · exact admission22_01_pos hδ hp
 · exact admission22_02_pos hδ hp
 · exact admission22_03_pos hδ hp
 · exact admission22_04_pos hδ hp
 · exact admission22_05_pos hδ hp
 · exact admission22_06_pos hδ hp
 · exact admission22_07_pos hδ hp
 · exact admission22_08_pos hδ hp
 · exact admission22_09_pos hδ hp
 · exact admission22_10_pos hδ hp
 · exact admission22_11_pos hδ hp
 · exact admission22_12_pos hδ hp
 · exact admission22_13_pos hδ hp
 · exact admission22_14_pos hδ hp
#print axioms admission22_all
end
end RH20261023Finite
