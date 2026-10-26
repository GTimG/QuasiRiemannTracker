/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission37_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(753122667991893993/786981005458153:ℝ),(751335686986435840/786981005458153:ℝ)]
]
theorem admission37_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission37_00_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission37_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_00_coefficients]
def admission37_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(550868549589148672/786981005458153:ℝ),(549868549589148672/786981005458153:ℝ)]
]
theorem admission37_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission37_01_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission37_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_01_coefficients]
def admission37_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(280245931308247286/786981005458153:ℝ),(279764800549477376/786981005458153:ℝ)]
]
theorem admission37_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission37_02_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission37_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_02_coefficients]
def admission37_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(573394781500174793687040/786981005458153:ℝ),(10303582007280860745023488/7082829049123377:ℝ),(5143034589779287601840128/7082829049123377:ℝ)],
  ![(572418894276555450475520/786981005458153:ℝ),(10286017982438766264878080/7082829049123377:ℝ),(5134253558949767210598400/7082829049123377:ℝ)]
]
theorem admission37_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (19585623012351101725/38681690380279136256:ℝ) admission37_03_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission37_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_03_coefficients]
def admission37_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(89884658798488529098656/786981005458153:ℝ),(179265855170846484578304/786981005458153:ℝ),(89381496597951427903488/786981005458153:ℝ)],
  ![(90171944303931541850262/786981005458153:ℝ),(179839619350921403393024/786981005458153:ℝ),(89667975753714092736512/786981005458153:ℝ)]
]
theorem admission37_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (31965314125282083/402934274794574336:ℝ) admission37_04_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission37_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_04_coefficients]
def admission37_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(20084525133109577520255197/295117877046807375:ℝ),(200876897020799109742009954/1475589385234036875:ℝ),(33484666938421153782011323/491863128411345625:ℝ)],
  ![(1807758203375001821608489/26828897913346125:ℝ),(7955466485592683723673586/59023575409361475:ℝ),(6630645998709770627672767/98372625682269125:ℝ)]
]
theorem admission37_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1807758203375001821608489/38409746375181416267776000:ℝ) admission37_05_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission37_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_05_coefficients]
def admission37_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(34777167171108497399755022935138522647298048/206239921282991172178485579079197:ℝ),(3151726793614567707687250975273233625186304/6249694584333065823590472093309:ℝ),(103682872937126542890360685190214282698031104/206239921282991172178485579079197:ℝ),(103462629965329463553437250658666954096640/619339102951925441977434171409:ℝ)],
  ![(3170860582869090144466264691492146800005120/18749083752999197470771416279927:ℝ),(34771184848931219325791091393022005235486720/68746640427663724059495193026399:ℝ),(9453556033170072771452499911595116666552320/18749083752999197470771416279927:ℝ),(103768853119856996750461224339020667944960/619339102951925441977434171409:ℝ)]
]
theorem admission37_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (72267812186849394501259492704645/634203241422771652584892591522816:ℝ) admission37_06_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission37_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_06_coefficients]
def admission37_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(651886139500474355130106948690225614368/1858017308855776325932302514227:ℝ),(3903342426568778642628450184343952769024/5574051926567328977796907542681:ℝ),(1947687983650896718852123382646180413440/5574051926567328977796907542681:ℝ)],
  ![(649358601027211706091244043001222290030/1858017308855776325932302514227:ℝ),(3888192716856777706741589731950887971840/5574051926567328977796907542681:ℝ),(1940120881620739986510371122579780403200/5574051926567328977796907542681:ℝ)]
]
theorem admission37_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (3700486911050300572415106053504525/15220877794146519662037422196547584:ℝ) admission37_07_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission37_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_07_coefficients]
def admission37_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(2281106881596157229552720823049036500712004282931552260453/680426260567300900609974065268676757812500000000:ℝ),(1047411046333766027411278775653071070788701561513060672743/103094887964742560698480918980102539062500000000:ℝ),(34912437481316877737527120203811080978742553095910664356629/3402131302836504503049870326343383789062500000000:ℝ),(94027255488653481262498123786128417779394080079474387667/27217050422692036024398962610747070312500000000:ℝ)],
  ![(359632446490108275931031902115917845742141047803893657117/98971092446152858270541682220898437500000000000:ℝ),(19962980758730757381611052519516265355216992050619530758489/1814470028179469068293264174049804687500000000000:ℝ),(7554799595624722146953081079282219965843231182796401675601/680426260567300900609974065268676757812500000000:ℝ),(2541154795743880478016956342672641800188765772373073096347/680426260567300900609974065268676757812500000000:ℝ)]
]
theorem admission37_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (2281106881596157229552720823049036500712004282931552260453/997515447117186312571284501072942465024000000000000000000000:ℝ) admission37_08_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission37_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_08_coefficients]
def admission37_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(142736427574678866770079132940662867344869756576/10886820169076814409759585044298828125:ℝ),(2130378338663890223241568155608825992069486750144/54434100845384072048797925221494140625:ℝ),(706572069552246820600184589508476854702742765568/18144700281794690682932641740498046875:ℝ),(140604002701972290096971987130381689775430565888/10886820169076814409759585044298828125:ℝ)],
  ![(139373418240103354095593537045675411593589563558/10886820169076814409759585044298828125:ℝ),(416001363094351577784609115609342626045088954868/10886820169076814409759585044298828125:ℝ),(27592243079451185743070301407404965242817163264/725788011271787627317305669619921875:ℝ),(5490228098722071585424816179716719574954541056/435472806763072576390383401771953125:ℝ)]
]
theorem admission37_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (10471779057926314516877777442391814374837/1217670223531721572962993775723806720000000:ℝ) admission37_09_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission37_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_09_coefficients]
def admission37_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(66092730543402869452366278403948544/13833650486569095703125:ℝ),(328462231726443331508851059057098752/23056084144281826171875:ℝ),(108820542640764233780753297391484928/7685361381427275390625:ℝ),(324461843631692456762057891371810816/69168252432845478515625:ℝ)],
  ![(130469942312023307406584693775613952/13833650486569095703125:ℝ),(43223804768404496125227510114369536/1537072276285455078125:ℝ),(386619633725491105466851934651809792/13833650486569095703125:ℝ),(8538355603614513183092602493206528/922243365771273046875:ℝ)],
  ![(11444289873838191862218036250112/2459315642056728125:ℝ),(102361425647221780604676925092352/7377946926170184375:ℝ),(305173502502314395388235651801088/22133840778510553125:ℝ),(20217567034452618566833440555008/4426768155702110625:ℝ)]
]
theorem admission37_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (9640487210489568026940079/4225072101269955789455360000:ℝ) admission37_10_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission37_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_10_coefficients]
def admission37_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1603978686139300402485937737817724138912/5574051926567328977796907542681:ℝ),(3201434417769523411625965472105850241024/5574051926567328977796907542681:ℝ),(1597459540421546971345348654611822804992/5574051926567328977796907542681:ℝ)],
  ![(1597604115802511022656058053019166307510/5574051926567328977796907542681:ℝ),(3188698580482257838750739055368455813120/5574051926567328977796907542681:ℝ),(1591098265465831814889725447413331394560/5574051926567328977796907542681:ℝ)]
]
theorem admission37_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (6069558202613188991125966825154615/30441755588293039324074844393095168:ℝ) admission37_11_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission37_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_11_coefficients]
def admission37_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission37_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission37_12_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission37_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_12_coefficients]
def admission37_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission37_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission37_13_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission37_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_13_coefficients]
def admission37_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission37_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission37_14_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission37_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_14_coefficients]
theorem admission37_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission37_00_pos hδ hp
 · exact admission37_01_pos hδ hp
 · exact admission37_02_pos hδ hp
 · exact admission37_03_pos hδ hp
 · exact admission37_04_pos hδ hp
 · exact admission37_05_pos hδ hp
 · exact admission37_06_pos hδ hp
 · exact admission37_07_pos hδ hp
 · exact admission37_08_pos hδ hp
 · exact admission37_09_pos hδ hp
 · exact admission37_10_pos hδ hp
 · exact admission37_11_pos hδ hp
 · exact admission37_12_pos hδ hp
 · exact admission37_13_pos hδ hp
 · exact admission37_14_pos hδ hp
#print axioms admission37_all
end
end RH20261023Finite
