/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission47_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(377454824498676073/786981005458153:ℝ),(375667843493217920/786981005458153:ℝ)]
]
theorem admission47_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission47_00_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission47_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_00_coefficients]
def admission47_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(275934274794574336/786981005458153:ℝ),(274934274794574336/786981005458153:ℝ)]
]
theorem admission47_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission47_01_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission47_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_01_coefficients]
def admission47_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(140363531033508598/786981005458153:ℝ),(139882400274738688/786981005458153:ℝ)]
]
theorem admission47_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission47_02_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission47_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_02_coefficients]
def admission47_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(646710551634610462282240/7082829049123377:ℝ),(143226471547797376451072/786981005458153:ℝ),(642330509295565925777408/7082829049123377:ℝ)],
  ![(644514321335703515640832/7082829049123377:ℝ),(142738527435987704845312/786981005458153:ℝ),(58194113780744166178816/643893549920307:ℝ)]
]
theorem admission47_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (443985853429749803/879129326824525824:ℝ) admission47_03_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission47_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_03_coefficients]
def admission47_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(11334765991152458341062/786981005458153:ℝ),(22543112366439224951296/786981005458153:ℝ),(11208496969214261592064/786981005458153:ℝ)],
  ![(11406789195498677893564/786981005458153:ℝ),(22686754878595351942144/786981005458153:ℝ),(11280116758154927800320/786981005458153:ℝ)]
]
theorem admission47_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (256542136441366461/3223474198356594688:ℝ) admission47_04_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission47_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_04_coefficients]
def admission47_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(378442065570988432681032/44714829855576875:ℝ),(2271457317554036579133436/134144489566730625:ℝ),(2499461325140046200212498/295117877046807375:ℝ)],
  ![(4079734471918871236004834/491863128411345625:ℝ),(24488068469911845010853876/1475589385234036875:ℝ),(1113520810640545956211534/134144489566730625:ℝ)]
]
theorem admission47_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (6119601707878306854007251/132033503164686118420480000:ℝ) admission47_05_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission47_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_05_coefficients]
def admission47_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(244481753293527492776530618602746392909824/22915546809221241353165064342133:ℝ),(6560259044593952114475161021976862408726528/206239921282991172178485579079197:ℝ),(6519612590984185317613997700108012524142592/206239921282991172178485579079197:ℝ),(6485553319991062296903826521188791746560/619339102951925441977434171409:ℝ)],
  ![(245907128829515071343749866229270385651712/22915546809221241353165064342133:ℝ),(6598662125899910836492118814169685146169344/206239921282991172178485579079197:ℝ),(6557933831498624008539832446106842665844736/206239921282991172178485579079197:ℝ),(6523831214307003946531823231233005977600/619339102951925441977434171409:ℝ)]
]
theorem admission47_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (579853652714883890471204506265115/5073625931382173220679140732182528:ℝ) admission47_06_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission47_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_06_coefficients]
def admission47_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(22270354193109698813640481150499564174/506731993324302634345173412971:ℝ),(162653323383285717933228233928670233088/1858017308855776325932302514227:ℝ),(242988054079477294085155906576622551040/5574051926567328977796907542681:ℝ)],
  ![(243074360052880024691448736768417628932/5574051926567328977796907542681:ℝ),(161389555436311684009043535207559435264/1858017308855776325932302514227:ℝ),(241096278571938110999717841560022548480/5574051926567328977796907542681:ℝ)]
]
theorem admission47_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (919709314620735591887351385345545/3805219448536629915509355549136896:ℝ) admission47_07_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission47_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_07_coefficients]
def admission47_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(2709514153032596829277267908340201136558585722253166890767/12096466854529793788621761160332031250000000000000:ℝ),(74513609174513060585963632988036107541833179692600742748921/108868201690768144097595850442988281250000000000000:ℝ),(15173942417516651937993273160313588875251392526509175265967/21773640338153628819519170088597656250000000000000:ℝ),(780052226708558790204436150374220798091502022928178351449/3299036414871761942351389407363281250000000000000:ℝ)],
  ![(125470413187715797034822250464314172627097550722976709797/483858674181191751544870446413281250000000000000:ℝ),(86013436034952198392597646828268122556565697866321930233591/108868201690768144097595850442988281250000000000000:ℝ),(87333791550384516880602452461202213837810958953943824220523/108868201690768144097595850442988281250000000000000:ℝ),(9850397217311103001945485974245971150365947388118051230419/36289400563589381365865283480996093750000000000000:ℝ)]
]
theorem admission47_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (8128542459097790487831803725020603409675757166759500672301/3325051490390621041904281670243141550080000000000000000000000:ℝ) admission47_08_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission47_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_08_coefficients]
def admission47_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(44730683388014596583437580610215744559107898428/54434100845384072048797925221494140625:ℝ),(26575099310624165222157114609648647223599151434/10886820169076814409759585044298828125:ℝ),(43853463089023265043465857639203070189156322304/18144700281794690682932641740498046875:ℝ),(8683115786563252491643512238228114973415440384/10886820169076814409759585044298828125:ℝ)],
  ![(42619591532928130391045338322235166751472057944/54434100845384072048797925221494140625:ℝ),(25312132173480897224326129661394290478301419236/10886820169076814409759585044298828125:ℝ),(41754652593731783575953833206779702032057300992/18144700281794690682932641740498046875:ℝ),(751325296120289993997687673504104765747232768/989710924461528582705416822208984375:ℝ)]
]
theorem admission47_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5732157105409927322370053661377752424219/691858081552114530092610099843072000000000:ℝ) admission47_09_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission47_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_09_coefficients]
def admission47_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1153220879606398889573026481018624/7685361381427275390625:ℝ),(30765240423180901001301467647354624/69168252432845478515625:ℝ),(1215752615819221850289362107488256/2766730097313819140625:ℝ),(3335854491425028941529941123006464/23056084144281826171875:ℝ)],
  ![(808643754970500283383440641297408/2766730097313819140625:ℝ),(605138386180690669813107658097664/698669216493388671875:ℝ),(597673819574363821826282120060928/698669216493388671875:ℝ),(1770645723183016398535480706072576/6288022948440498046875:ℝ)],
  ![(9835172125033941330216725150620672/69168252432845478515625:ℝ),(5827534890753635025246127042137088/13833650486569095703125:ℝ),(28770123504447937747425026089508864/69168252432845478515625:ℝ),(9467621764978860201411116029444096/69168252432845478515625:ℝ)]
]
theorem admission47_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (9029027714709148599063030271/4126046973896441200640000000000:ℝ) admission47_10_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission47_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_10_coefficients]
def admission47_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(18264449982006720825809377802646457202/506731993324302634345173412971:ℝ),(400191916279612085531211302303489629184/5574051926567328977796907542681:ℝ),(199284862867961174139692131376572137472/5574051926567328977796907542681:ℝ)],
  ![(199311979369988546577730877599627559164/5574051926567328977796907542681:ℝ),(397004635113836877321409697534038120448/5574051926567328977796907542681:ℝ),(197694544129032385025786329576949284864/5574051926567328977796907542681:ℝ)]
]
theorem admission47_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1508289673836001472669878613105387/7610438897073259831018711098273792:ℝ) admission47_11_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission47_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_11_coefficients]
def admission47_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission47_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission47_12_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission47_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_12_coefficients]
def admission47_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission47_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission47_13_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission47_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_13_coefficients]
def admission47_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission47_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission47_14_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission47_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_14_coefficients]
theorem admission47_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission47_00_pos hδ hp
 · exact admission47_01_pos hδ hp
 · exact admission47_02_pos hδ hp
 · exact admission47_03_pos hδ hp
 · exact admission47_04_pos hδ hp
 · exact admission47_05_pos hδ hp
 · exact admission47_06_pos hδ hp
 · exact admission47_07_pos hδ hp
 · exact admission47_08_pos hδ hp
 · exact admission47_09_pos hδ hp
 · exact admission47_10_pos hδ hp
 · exact admission47_11_pos hδ hp
 · exact admission47_12_pos hδ hp
 · exact admission47_13_pos hδ hp
 · exact admission47_14_pos hδ hp
#print axioms admission47_all
end
end RH20261023Finite
