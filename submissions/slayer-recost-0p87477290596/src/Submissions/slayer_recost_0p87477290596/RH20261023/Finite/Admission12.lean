/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission12_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(95703941878762633/786981005458153:ℝ),(93916960873304480/786981005458153:ℝ)]
]
theorem admission12_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission12_00_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission12_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_00_coefficients]
def admission12_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(69733568698643584/786981005458153:ℝ),(68733568698643584/786981005458153:ℝ)]
]
theorem admission12_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission12_01_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission12_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_01_coefficients]
def admission12_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(35451730827454582/786981005458153:ℝ),(34970600068684672/786981005458153:ℝ)]
]
theorem admission12_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission12_02_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission12_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_02_coefficients]
def admission12_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(10517032346734237758976/7082829049123377:ℝ),(6919522654848113172992/2360943016374459:ℝ),(10242219617810101760000/7082829049123377:ℝ)],
  ![(10379592342141269438080/7082829049123377:ℝ),(6827971784413371694976/2360943016374459:ℝ),(10105016011098845646848/7082829049123377:ℝ)]
]
theorem admission12_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2467044924584679113/4835211297534892032:ℝ) admission12_03_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission12_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_03_coefficients]
def admission12_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(177789315892845670152/786981005458153:ℝ),(347849748689261401600/786981005458153:ℝ),(170096998734082244608/786981005458153:ℝ)],
  ![(182366767401094721662/786981005458153:ℝ),(356902955875543321216/786981005458153:ℝ),(174573235542873882624/786981005458153:ℝ)]
]
theorem admission12_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (15572845343086143/201467137397287168:ℝ) admission12_04_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission12_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_04_coefficients]
def admission12_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(14569558150709448314287/98372625682269125:ℝ),(437235351877476754051922/1475589385234036875:ℝ),(218659029233710317162617/1475589385234036875:ℝ)],
  ![(67601726814517779975469/491863128411345625:ℝ),(405961486827171970174298/1475589385234036875:ℝ),(203122922442821224491641/1475589385234036875:ℝ)]
]
theorem admission12_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (202805180443553339926407/4126046973896441200640000:ℝ) admission12_05_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission12_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_05_coefficients]
def admission12_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(2946835814679310331017796731796426627072/68746640427663724059495193026399:ℝ),(213941955602039060224758273855977359360/1704462159363563406433765116357:ℝ),(25258712197988064432124165353506686173184/206239921282991172178485579079197:ℝ),(24661339045192675287413442679647764480/619339102951925441977434171409:ℝ)],
  ![(3014942672845915015544073000404152523264/68746640427663724059495193026399:ℝ),(26494727820713012878705269747835300318720/206239921282991172178485579079197:ℝ),(25861307710376777553502803540894350491648/206239921282991172178485579079197:ℝ),(25259431143879263562850891274088611840/619339102951925441977434171409:ℝ)]
]
theorem admission12_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (35278328483380330020065464038345/317101620711385826292446295761408:ℝ) admission12_06_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission12_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_06_coefficients]
def admission12_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(4102907061622272606830346150616728952/5574051926567328977796907542681:ℝ),(897381881846197099606713417653252608/619339102951925441977434171409:ℝ),(32843324783666373011077517649305600/46066544847663875849561219361:ℝ)],
  ![(3982725147996396192090450814200945634/5574051926567328977796907542681:ℝ),(870891865745826901151241233252352896/619339102951925441977434171409:ℝ),(3855806329602432191500500572028477440/5574051926567328977796907542681:ℝ)]
]
theorem admission12_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (470679483594046898376525948733945/1902609724268314957754677774568448:ℝ) admission12_07_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission12_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_07_coefficients]
def admission12_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(5934689910214663734807789791633631715066505254011856399/36289400563589381365865283480996093750000000000000:ℝ),(79765147985377762840148377003105401591485644743041218771/108868201690768144097595850442988281250000000000000:ℝ),(106042010743795826593879509511854841061784283482212169337/108868201690768144097595850442988281250000000000000:ℝ),(4897697687792156870702620197022058759622952930689613307/12096466854529793788621761160332031250000000000000:ℝ)],
  ![(4822716831426233081299136938793500275020532788792286649/6598072829743523884702778814726562500000000000000:ℝ),(525622897991677194939980989724420341887278010565566465701/217736403381536288195191700885976562500000000000000:ℝ),(474116554851501583231974447412142139655622436955964813/179947440811187015037348513128906250000000000000:ℝ),(11511357706109637650372871864363425277119958846877578747/12096466854529793788621761160332031250000000000000:ℝ)]
]
theorem admission12_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (5934689910214663734807789791633631715066505254011856399/12988482384338363444938600274387271680000000000000000000000:ℝ) admission12_08_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission12_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_08_coefficients]
def admission12_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(241858661992174837252430129156798970513150302/54434100845384072048797925221494140625:ℝ),(63840653633325064267786882873553522806513586/4948554622307642913527084111044921875:ℝ),(20576585228028487918786027023504057983514368/1649518207435880971175694703681640625:ℝ),(69964631012522673985357495102036814216192/17418912270522903055615336070878125:ℝ)],
  ![(416006922258691235765553991306248643917282673/108868201690768144097595850442988281250:ℝ),(1203694949999300806050030369059865733332897869/108868201690768144097595850442988281250:ℝ),(193261514968235437340804417814028475702128576/18144700281794690682932641740498046875:ℝ),(37188245488450693777271124599976719038309376/10886820169076814409759585044298828125:ℝ)]
]
theorem admission12_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (36316645984815130641866332617164764685849/3805219448536629915509355549136896000000000:ℝ) admission12_09_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission12_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_09_coefficients]
def admission12_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1597990099557620625193944630272/7685361381427275390625:ℝ),(41554485283755032830529303600128/69168252432845478515625:ℝ),(39968814328156315096323782182912/69168252432845478515625:ℝ),(387765892758935390683029704704/2096007649480166015625:ℝ)],
  ![(26740936875775719181815910495744/69168252432845478515625:ℝ),(25698937209382487420981303389696/23056084144281826171875:ℝ),(24660512296447064800088736283648/23056084144281826171875:ℝ),(945029283466278052765528367104/2766730097313819140625:ℝ)],
  ![(224146352937636742661807641792/1257604589688099609375:ℝ),(3222765045337835830456918751296/6288022948440498046875:ℝ),(3083802178998288454382167875712/6288022948440498046875:ℝ),(981772119715823837234287333376/6288022948440498046875:ℝ)]
]
theorem admission12_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (239690458914996054012277181/93773794861282754560000000000:ℝ) admission12_10_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission12_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_10_coefficients]
def admission12_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(3368534456914164864687989661382646920/5574051926567328977796907542681:ℝ),(6630960711607210093831282573084513280/5574051926567328977796907542681:ℝ),(296628942189678847760123497406689280/506731993324302634345173412971:ℝ)],
  ![(3267470608512744639294901496699953822/5574051926567328977796907542681:ℝ),(6430509947261703959095557055580205824/5574051926567328977796907542681:ℝ),(3163523442903418005742245858997153792/5574051926567328977796907542681:ℝ)]
]
theorem admission12_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (772344590552592286558165492919227/3805219448536629915509355549136896:ℝ) admission12_11_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission12_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_11_coefficients]
def admission12_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission12_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission12_12_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission12_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_12_coefficients]
def admission12_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission12_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission12_13_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission12_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_13_coefficients]
def admission12_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission12_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission12_14_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission12_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_14_coefficients]
theorem admission12_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission12_00_pos hδ hp
 · exact admission12_01_pos hδ hp
 · exact admission12_02_pos hδ hp
 · exact admission12_03_pos hδ hp
 · exact admission12_04_pos hδ hp
 · exact admission12_05_pos hδ hp
 · exact admission12_06_pos hδ hp
 · exact admission12_07_pos hδ hp
 · exact admission12_08_pos hδ hp
 · exact admission12_09_pos hδ hp
 · exact admission12_10_pos hδ hp
 · exact admission12_11_pos hδ hp
 · exact admission12_12_pos hδ hp
 · exact admission12_13_pos hδ hp
 · exact admission12_14_pos hδ hp
#print axioms admission12_all
end
end RH20261023Finite
