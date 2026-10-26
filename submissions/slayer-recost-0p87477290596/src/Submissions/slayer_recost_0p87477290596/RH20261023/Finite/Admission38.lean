/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission38_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(753122667991893993/786981005458153:ℝ),(751335686986435840/786981005458153:ℝ)]
]
theorem admission38_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission38_00_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission38_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_00_coefficients]
def admission38_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(550868549589148672/786981005458153:ℝ),(549868549589148672/786981005458153:ℝ)]
]
theorem admission38_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission38_01_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission38_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_01_coefficients]
def admission38_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(280245931308247286/786981005458153:ℝ),(279764800549477376/786981005458153:ℝ)]
]
theorem admission38_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission38_02_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission38_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_02_coefficients]
def admission38_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(52082429938421810605056/71543727768923:ℝ),(10294799013268286656119808/7082829049123377:ℝ),(5138644074364527406219264/7082829049123377:ℝ)],
  ![(571930842099020573444096/786981005458153:ℝ),(10277234988426192175974400/7082829049123377:ℝ),(5129863043535007014977536/7082829049123377:ℝ)]
]
theorem admission38_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (9784437262601865797/19340845190139568128:ℝ) admission38_03_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission38_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_03_coefficients]
def admission38_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(90028704726050209433750/786981005458153:ℝ),(179553140195158738560000/786981005458153:ℝ),(89524736175832760320000/786981005458153:ℝ)],
  ![(90315990231493222185356/786981005458153:ℝ),(16375173125021241579520/71543727768923:ℝ),(8164655939235947741184/71543727768923:ℝ)]
]
theorem admission38_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (512264649443623125/6446948396713189376:ℝ) admission38_04_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission38_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_04_coefficients]
def admission38_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(19984932685117298778974288/295117877046807375:ℝ),(39976517323947976100929748/295117877046807375:ℝ),(1332768696274772708286614/19674525136453825:ℝ)],
  ![(3957149557826548259282494/59023575409361475:ℝ),(197892351738757863854478436/1475589385234036875:ℝ),(32987780461997017063517862/491863128411345625:ℝ)]
]
theorem admission38_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1978574778913274129641247/42250721012699557894553600:ℝ) admission38_05_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission38_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_05_coefficients]
def admission38_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(34828480256331157311824419988634721444311040/206239921282991172178485579079197:ℝ),(34720198693702385048486599775243111879741440/68746640427663724059495193026399:ℝ),(103836157899184297654064024174209603264839680/206239921282991172178485579079197:ℝ),(103615741542593230151949237498843811020800/619339102951925441977434171409:ℝ)],
  ![(34930779496782651501198308659909813597069312/206239921282991172178485579079197:ℝ),(34822388812873359589717930440259547238178816/68746640427663724059495193026399:ℝ),(104142401326928555249680838011541603898884096/206239921282991172178485579079197:ℝ),(103921964697120763348973211179197524869120/619339102951925441977434171409:ℝ)]
]
theorem admission38_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1157996150209679046481280447902275/10147251862764346441358281464365056:ℝ) admission38_06_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission38_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_06_coefficients]
def admission38_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(650619784698904494814869419678955625070/1858017308855776325932302514227:ℝ),(3895759818886934439083341992017287982080/5574051926567328977796907542681:ℝ),(1943904432635818352681247252612980408320/5574051926567328977796907542681:ℝ)],
  ![(648092246225641845776006513989952300732/1858017308855776325932302514227:ℝ),(3880610109174933503196481539624223184896/5574051926567328977796907542681:ℝ),(1936337330605661620339494992546580398080/5574051926567328977796907542681:ℝ)]
]
theorem admission38_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1846635180097257252063269608065205/7610438897073259831018711098273792:ℝ) admission38_07_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission38_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_07_coefficients]
def admission38_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(38028639609725213012628521200767773521513791892666569225059/10886820169076814409759585044298828125000000000000:ℝ),(38395032013274817423437117007049341200312260735477328459167/3628940056358938136586528348099609375000000000000:ℝ),(10571273183403223848354030288415086447556957166132475239653/989710924461528582705416822208984375000000000000:ℝ),(39127547227715390308486313450779079292898528992207436483741/10886820169076814409759585044298828125000000000000:ℝ)],
  ![(41090498618098607692198497264734152541757238624190035340681/10886820169076814409759585044298828125000000000000:ℝ),(207260623498938840108911045715468851094919749357283271477957/18144700281794690682932641740498046875000000000000:ℝ),(627204993036085039615284228944430056223210289226427642522931/54434100845384072048797925221494140625000000000000:ℝ),(42175121764156085451758365419089980984161149318386850958493/10886820169076814409759585044298828125000000000000:ℝ)]
]
theorem admission38_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (38028639609725213012628521200767773521513791892666569225059/15960247153874981001140552017167079440384000000000000000000000:ℝ) admission38_08_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission38_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_08_coefficients]
def admission38_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(141047568357063604326269328364407261794373083302/10886820169076814409759585044298828125:ℝ),(16840952537809293139065459582621527065897580564/435472806763072576390383401771953125:ℝ),(139635365514216178946027298355756676414869336064/3628940056358938136586528348099609375:ℝ),(138929852585012039866296195811649839574647046144/10886820169076814409759585044298828125:ℝ)],
  ![(137684559022488091651783732469419806043092890284/10886820169076814409759585044298828125:ℝ),(2054747544034029308064659870265578021393155594696/54434100845384072048797925221494140625:ℝ),(681410835005113717706709437455430658442032996352/18144700281794690682932641740498046875:ℝ),(135581552351091539404944613174186139173080006656/10886820169076814409759585044298828125:ℝ)]
]
theorem admission38_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (129300644255725421338028538870035304234581/15220877794146519662037422196547584000000000:ℝ) admission38_09_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission38_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_09_coefficients]
def admission38_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(326167173786958158815639747830984192/69168252432845478515625:ℝ),(9823514431297790214556753612429824/698669216493388671875:ℝ),(87868796234137229423682622433468416/6288022948440498046875:ℝ),(106732001999527059265843328989528064/23056084144281826171875:ℝ)],
  ![(643725941417198072848120565852698624/69168252432845478515625:ℝ),(639753791234722841061563868532025344/23056084144281826171875:ℝ),(635783246387676163721076948011352064/23056084144281826171875:ℝ),(631814311552718197076659804290678784/69168252432845478515625:ℝ)],
  ![(35282595720981874487363445633087488/7685361381427275390625:ℝ),(315562430349839718001244797576996864/23056084144281826171875:ℝ),(940746891046674029783478412408619008/69168252432845478515625:ℝ),(311602963828063152416015030375415808/69168252432845478515625:ℝ)]
]
theorem admission38_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (37145967939861196567537192151/16504187895585764802560000000000:ℝ) admission38_10_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission38_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_10_coefficients]
def admission38_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1600784753280368600883869656618412012726/5574051926567328977796907542681:ℝ),(3195059855437972995206362262566947223552/5574051926567328977796907542681:ℝ),(1594278902943689393117537051012577099776/5574051926567328977796907542681:ℝ)],
  ![(1594410182943579221053989971819854181324/5574051926567328977796907542681:ℝ),(3182324018150707422331135845829552795648/5574051926567328977796907542681:ℝ),(1587917627987974236661913843814085689344/5574051926567328977796907542681:ℝ)]
]
theorem admission38_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (3028712516761730645488574683788463/15220877794146519662037422196547584:ℝ) admission38_11_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission38_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_11_coefficients]
def admission38_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission38_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission38_12_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission38_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_12_coefficients]
def admission38_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission38_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission38_13_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission38_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_13_coefficients]
def admission38_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission38_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission38_14_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission38_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_14_coefficients]
theorem admission38_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission38_00_pos hδ hp
 · exact admission38_01_pos hδ hp
 · exact admission38_02_pos hδ hp
 · exact admission38_03_pos hδ hp
 · exact admission38_04_pos hδ hp
 · exact admission38_05_pos hδ hp
 · exact admission38_06_pos hδ hp
 · exact admission38_07_pos hδ hp
 · exact admission38_08_pos hδ hp
 · exact admission38_09_pos hδ hp
 · exact admission38_10_pos hδ hp
 · exact admission38_11_pos hδ hp
 · exact admission38_12_pos hδ hp
 · exact admission38_13_pos hδ hp
 · exact admission38_14_pos hδ hp
#print axioms admission38_all
end
end RH20261023Finite
