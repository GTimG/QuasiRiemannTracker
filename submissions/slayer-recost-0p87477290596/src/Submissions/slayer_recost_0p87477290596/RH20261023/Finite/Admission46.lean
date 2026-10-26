/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission46_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(273375429904654683/71543727768923:ℝ),(3005342747945743360/786981005458153:ℝ)]
]
theorem admission46_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission46_00_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission46_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_00_coefficients]
def admission46_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(200043108941508608/71543727768923:ℝ),(2199474198356594688/786981005458153:ℝ)]
]
theorem admission46_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission46_01_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission46_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_01_coefficients]
def admission46_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(101776393905152674/71543727768923:ℝ),(1119059202197909504/786981005458153:ℝ)]
]
theorem admission46_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission46_02_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission46_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_02_coefficients]
def admission46_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(109577301360314613448462336/2360943016374459:ℝ),(657183612833456615563816960/7082829049123377:ℝ),(328451731279512775218429952/7082829049123377:ℝ)],
  ![(109530466581313099764957184/2360943016374459:ℝ),(656902611994179748253433856/7082829049123377:ℝ),(328311234786240448958562304/7082829049123377:ℝ)]
]
theorem admission46_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (9784437262601865797/19340845190139568128:ℝ) admission46_03_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission46_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_03_coefficients]
def admission46_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(5744528175180376374061370/786981005458153:ℝ),(11480985585901687789449216/786981005458153:ℝ),(5736458614991600616472576/786981005458153:ℝ)],
  ![(5749115065627908126754352/786981005458153:ℝ),(11490156142360291420700672/786981005458153:ℝ),(5741042281483803253800960/786981005458153:ℝ)]
]
theorem admission46_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2051517468091821891/25787793586852757504:ℝ) admission46_04_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission46_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_04_coefficients]
def admission46_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(6348186806167373079688757242/1475589385234036875:ℝ),(1154265329673550057156197296/134144489566730625:ℝ),(2116243578348940932331848088/491863128411345625:ℝ)],
  ![(6332271379532952124946955064/1475589385234036875:ℝ),(12665094226854316915774869904/1475589385234036875:ℝ),(422188117446196824406697656/98372625682269125:ℝ)]
]
theorem admission46_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (791533922441619015618369383/16900288405079823157821440000:ℝ) admission46_05_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission46_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_05_coefficients]
def admission46_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(8863584306038268857667709338587121698117140480/206239921282991172178485579079197:ℝ),(8856662061744972157396991505426014200676335616/68746640427663724059495193026399:ℝ),(26549225956587145975298477543439905630116118528/206239921282991172178485579079197:ℝ),(26555027257738510105813306273017972150763520/619339102951925441977434171409:ℝ)],
  ![(806374159962119499278469006830872086855680000/18749083752999197470771416279927:ℝ),(8863191772820086184292774735264816268796100608/68746640427663724059495193026399:ℝ),(26568809864136958368692040150757538926715469824/206239921282991172178485579079197:ℝ),(26574625539628272230422840588560609837056000/619339102951925441977434171409:ℝ)]
]
theorem admission46_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (4637118066498982389308507485492965/40589007451057385765433125857460224:ℝ) admission46_06_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission46_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_06_coefficients]
def admission46_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(13797078647715324873971624087765644957238/619339102951925441977434171409:ℝ),(248220354772514216923484719969625148608512/5574051926567328977796907542681:ℝ),(124046662791244851419195715684043545640960/5574051926567328977796907542681:ℝ)],
  ![(13783619129623413613321297375005222239824/619339102951925441977434171409:ℝ),(22543467771358404691248656719859935379456/506731993324302634345173412971:ℝ),(123925589158762343701727679522981145477120/5574051926567328977796907542681:ℝ)]
]
theorem admission46_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1846635180097257252063269608065205/7610438897073259831018711098273792:ℝ) admission46_07_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission46_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_07_coefficients]
def admission46_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(12667178860102597184720200648305522238692800577678290031265057/13608525211346018012199481305373535156250000000000:ℝ),(2539238783474358109528951400075252879018129873197789246029569/907235014089734534146632087024902343750000000000:ℝ),(3470511065040290823587375415095799960171331671065231882719991/1237138655576910728381771027761230468750000000000:ℝ),(12754218816624162712421838912584087067822170983764451269491423/13608525211346018012199481305373535156250000000000:ℝ)],
  ![(46950073800277274441043837911927540544092089186660310555861/49485546223076429135270841110449218750000000000:ℝ),(12940190170842002037995349925793677719505981016525199519377839/4536175070448672670733160435124511718750000000000:ℝ),(1556293000151926203882933966907046522909689224831456453309733/544341008453840720487979252214941406250000000000:ℝ),(12998024779539418323883603070048959203123180609858804427471583/13608525211346018012199481305373535156250000000000:ℝ)]
]
theorem admission46_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (12667178860102597184720200648305522238692800577678290031265057/5107279089239993920364976645493465420922880000000000000000000000:ℝ) admission46_08_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission46_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_08_coefficients]
def admission46_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(175289702106109482229049293286771757599355038832806/54434100845384072048797925221494140625:ℝ),(525195153948210181075337933213415584353197761313904/54434100845384072048797925221494140625:ℝ),(174840431634571550705075445346531187420940026576896/18144700281794690682932641740498046875:ℝ),(34923168616850346117192322261389328454008772231168/10886820169076814409759585044298828125:ℝ)],
  ![(174217070158999826320806303451822358642782492142288/54434100845384072048797925221494140625:ℝ),(521978434264374944743247240367655338587448806841472/54434100845384072048797925221494140625:ℝ),(173768583697375155761976232644366255746446918156288/18144700281794690682932641740498046875:ℝ),(34708877401879434087665820972591651628308481703936/10886820169076814409759585044298828125:ℝ)]
]
theorem admission46_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (129300644255725421338028538870035304234581/15220877794146519662037422196547584000000000:ℝ) admission46_09_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission46_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_09_coefficients]
def admission46_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(64561290365304244991794163882103216128/13833650486569095703125:ℝ),(322298983000154451438496335572277127168/23056084144281826171875:ℝ),(87761336045772216046758267853850411008/6288022948440498046875:ℝ),(35698244374110607223265028787337691136/7685361381427275390625:ℝ)],
  ![(643409151165645382712112808076092407808/69168252432845478515625:ℝ),(642394870318556487887231762717665755136/23056084144281826171875:ℝ),(213793563990278731904134052959106367488/7685361381427275390625:ℝ),(640366616197400860562623996555052449792/69168252432845478515625:ℝ)],
  ![(35622412937626961272322107947919212544/7685361381427275390625:ℝ),(106698301587109464518663187109823512576/7685361381427275390625:ℝ),(191752886553561210958213820712312897536/13833650486569095703125:ℝ),(319081434959936668073999391104425787392/69168252432845478515625:ℝ)]
]
theorem admission46_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (37145967939861196567537192151/16504187895585764802560000000000:ℝ) admission46_10_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission46_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_10_coefficients]
def admission46_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(101832397113949900978574656214338298898458/5574051926567328977796907542681:ℝ),(203560890525343071523277765179138442469376/5574051926567328977796907542681:ℝ),(101728508590521793649652457319277346684928/5574051926567328977796907542681:ℝ)],
  ![(101730563557149878472018488414541135089456/5574051926567328977796907542681:ℝ),(18487025143386985952440172958129551900672/506731993324302634345173412971:ℝ),(101626728191230351146362486004101484118016/5574051926567328977796907542681:ℝ)]
]
theorem admission46_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (3028712516761730645488574683788463/15220877794146519662037422196547584:ℝ) admission46_11_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission46_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_11_coefficients]
def admission46_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission46_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission46_12_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission46_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_12_coefficients]
def admission46_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission46_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission46_13_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission46_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_13_coefficients]
def admission46_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission46_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission46_14_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission46_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_14_coefficients]
theorem admission46_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission46_00_pos hδ hp
 · exact admission46_01_pos hδ hp
 · exact admission46_02_pos hδ hp
 · exact admission46_03_pos hδ hp
 · exact admission46_04_pos hδ hp
 · exact admission46_05_pos hδ hp
 · exact admission46_06_pos hδ hp
 · exact admission46_07_pos hδ hp
 · exact admission46_08_pos hδ hp
 · exact admission46_09_pos hδ hp
 · exact admission46_10_pos hδ hp
 · exact admission46_11_pos hδ hp
 · exact admission46_12_pos hδ hp
 · exact admission46_13_pos hδ hp
 · exact admission46_14_pos hδ hp
#print axioms admission46_all
end
end RH20261023Finite
