/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission36_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(377454824498676073/786981005458153:ℝ),(375667843493217920/786981005458153:ℝ)]
]
theorem admission36_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission36_00_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission36_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_00_coefficients]
def admission36_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(275934274794574336/786981005458153:ℝ),(274934274794574336/786981005458153:ℝ)]
]
theorem admission36_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission36_01_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission36_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_01_coefficients]
def admission36_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(140363531033508598/786981005458153:ℝ),(139882400274738688/786981005458153:ℝ)]
]
theorem admission36_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission36_02_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission36_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_02_coefficients]
def admission36_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(647809153079827360018432/7082829049123377:ℝ),(13042772557869528633344/71543727768923:ℝ),(643428138149255974682624/7082829049123377:ℝ)],
  ![(645612922780920413377024/7082829049123377:ℝ),(142982554024755143361024/786981005458153:ℝ),(641232880441875876872192/7082829049123377:ℝ)]
]
theorem admission36_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (9784437262601865797/19340845190139568128:ℝ) admission36_03_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission36_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_03_coefficients]
def admission36_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(11298552681276571892688/786981005458153:ℝ),(22471089643223764168704/786981005458153:ℝ),(11172687074743928487936/786981005458153:ℝ)],
  ![(1033688716874799222290/71543727768923:ℝ),(22614732155379891159552/786981005458153:ℝ),(11244306863684594696192/786981005458153:ℝ)]
]
theorem admission36_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (31965314125282083/402934274794574336:ℝ) admission36_04_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission36_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_04_coefficients]
def admission36_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(4204426845961873521234611/491863128411345625:ℝ),(25234607768190955159622162/1475589385234036875:ℝ),(1147381087301041290778939/134144489566730625:ℝ)],
  ![(4121298596599871997748093/491863128411345625:ℝ),(24736645745008397800008242/1475589385234036875:ℝ),(12372614251657228715832713/1475589385234036875:ℝ)]
]
theorem admission36_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (12363895789799615993244279/264067006329372236840960000:ℝ) admission36_05_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission36_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_05_coefficients]
def admission36_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(243764518802384834727429310112040363442176/22915546809221241353165064342133:ℝ),(594634161045346022404307962404647698153472/18749083752999197470771416279927:ℝ),(6500411158680559480677347310776267390844928/206239921282991172178485579079197:ℝ),(6466414372833091472089828166166684631040/619339102951925441977434171409:ℝ)],
  ![(245189894338372413294648557738564356184064/22915546809221241353165064342133:ℝ),(6579378852804764968464345378643947417131008/206239921282991172178485579079197:ℝ),(6538732399194998171603182056775097532547072/206239921282991172178485579079197:ℝ),(6504692267149033121717824876210898862080/619339102951925441977434171409:ℝ)]
]
theorem admission36_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (72267812186849394501259492704645/634203241422771652584892591522816:ℝ) admission36_06_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission36_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_06_coefficients]
def admission36_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(245927544441763757665922816034272781616/5574051926567328977796907542681:ℝ),(163286499494413357495600244310914363392/1858017308855776325932302514227:ℝ),(22175812893931535057079539916811141120/506731993324302634345173412971:ℝ)],
  ![(244028008370437095407326260147195204634/5574051926567328977796907542681:ℝ),(162022731547439323571415545589803565568/1858017308855776325932302514227:ℝ),(242042166325707702542436874068322549760/5574051926567328977796907542681:ℝ)]
]
theorem admission36_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1846635180097257252063269608065205/7610438897073259831018711098273792:ℝ) admission36_07_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission36_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_07_coefficients]
def admission36_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(311986383087805972622577966463296818374894899917817682961/1512058356816224223577720145041503906250000000000:ℝ),(8597700712373493385417376489614676305650647204683305224423/13608525211346018012199481305373535156250000000000:ℝ),(1754336400242400670083491797776174820820187060743370374257/2721705042269203602439896261074707031250000000000:ℝ),(993952629408454690930255232986045772040672085629218597837/4536175070448672670733160435124511718750000000000:ℝ)],
  ![(1461568620681372938786956042487013863059006122581896158923/6048233427264896894310880580166015625000000000000:ℝ),(40140716279713542444986512878574712729968847905593814640027/54434100845384072048797925221494140625000000000000:ℝ),(10204691934062160499246969821335157786795184843891595357621/13608525211346018012199481305373535156250000000000:ℝ),(1152680469848074229642341273002238568460600227617729768397/4536175070448672670733160435124511718750000000000:ℝ)]
]
theorem admission36_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (935959149263417917867733899389890455124684699753453048883/415631436298827630238035208780392693760000000000000000000000:ℝ) admission36_08_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission36_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_08_coefficients]
def admission36_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(45795431420000906381657453323988915991254039072/54434100845384072048797925221494140625:ℝ),(27210260153907339383484677813378560143603063728/10886820169076814409759585044298828125:ℝ),(44905929761214590116805512497419031970765643776/18144700281794690682932641740498046875:ℝ),(8892384551183283770477986153069596248513380352/10886820169076814409759585044298828125:ℝ)],
  ![(43684339564914440189265211036008338183618198588/54434100845384072048797925221494140625:ℝ),(5189458603352814277130738573024840679661066306/2177364033815362881951917008859765625:ℝ),(42807119265923108649293488064995663813666622464/18144700281794690682932641740498046875:ℝ),(8473847021943221212809038323386633698317500416/10886820169076814409759585044298828125:ℝ)]
]
theorem admission36_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (129300644255725421338028538870035304234581/15220877794146519662037422196547584000000000:ℝ) admission36_09_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission36_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_09_coefficients]
def admission36_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(10648965187691173874084292732633088/69168252432845478515625:ℝ),(701584958194904146081625077497856/1537072276285455078125:ℝ),(3466228471855749568887701784100864/7685361381427275390625:ℝ),(10273698897404733420400480302137344/69168252432845478515625:ℝ)],
  ![(6919972027423875438954743314886656/23056084144281826171875:ℝ),(61532436332946547824172090419023872/69168252432845478515625:ℝ),(12157145663234297359719631768813568/13833650486569095703125:ℝ),(6671069744263646763763432789901312/23056084144281826171875:ℝ)],
  ![(10109017061809476694567884659379968/69168252432845478515625:ℝ),(5991065571847312213306681327598336/13833650486569095703125:ℝ),(29583902831536206322465991677843456/69168252432845478515625:ℝ),(9737592619626973513000469699231744/69168252432845478515625:ℝ)]
]
theorem admission36_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (37145967939861196567537192151/16504187895585764802560000000000:ℝ) admission36_10_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission36_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_10_coefficients]
def admission36_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(201710760864694917033122533158783072976/5574051926567328977796907542681:ℝ),(401788878706458504627107105273318285312/5574051926567328977796907542681:ℝ),(18189092930675051699695002934216687616/506731993324302634345173412971:ℝ)],
  ![(200113790432609534526950254929299602918/5574051926567328977796907542681:ℝ),(398601597540683296417305500503866776576/5574051926567328977796907542681:ℝ),(198489703498496779582739230476760711168/5574051926567328977796907542681:ℝ)]
]
theorem admission36_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (3028712516761730645488574683788463/15220877794146519662037422196547584:ℝ) admission36_11_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission36_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_11_coefficients]
def admission36_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission36_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission36_12_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission36_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_12_coefficients]
def admission36_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission36_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission36_13_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission36_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_13_coefficients]
def admission36_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission36_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission36_14_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission36_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_14_coefficients]
theorem admission36_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission36_00_pos hδ hp
 · exact admission36_01_pos hδ hp
 · exact admission36_02_pos hδ hp
 · exact admission36_03_pos hδ hp
 · exact admission36_04_pos hδ hp
 · exact admission36_05_pos hδ hp
 · exact admission36_06_pos hδ hp
 · exact admission36_07_pos hδ hp
 · exact admission36_08_pos hδ hp
 · exact admission36_09_pos hδ hp
 · exact admission36_10_pos hδ hp
 · exact admission36_11_pos hδ hp
 · exact admission36_12_pos hδ hp
 · exact admission36_13_pos hδ hp
 · exact admission36_14_pos hδ hp
#print axioms admission36_all
end
end RH20261023Finite
