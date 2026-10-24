/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission09_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(95703941878762633/786981005458153:ℝ),(93916960873304480/786981005458153:ℝ)]
]
theorem admission09_00_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission09_00_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 0 := by
 rw [admission09_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_00_coefficients]
def admission09_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(69733568698643584/786981005458153:ℝ),(68733568698643584/786981005458153:ℝ)]
]
theorem admission09_01_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission09_01_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 1 := by
 rw [admission09_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_01_coefficients]
def admission09_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(35478855827454582/786981005458153:ℝ),(34998600068684672/786981005458153:ℝ)]
]
theorem admission09_02_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273426563036599/786981005458153:ℝ) admission09_02_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 2 := by
 rw [admission09_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_02_coefficients]
def admission09_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(5361655276282273172096/7082829049123377:ℝ),(3528444930073588712320/2360943016374459:ℝ),(5224012513938492964864/7082829049123377:ℝ)],
  ![(5224215271689304851200/7082829049123377:ℝ),(3436894059638847234304/2360943016374459:ℝ),(5086808907227236851712/7082829049123377:ℝ)]
]
theorem admission09_03_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (620948352933012311/1208802824383723008:ℝ) admission09_03_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 3 := by
 rw [admission09_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_03_coefficients]
def admission09_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(86621596467569602574/786981005458153:ℝ),(169480511967140419200/786981005458153:ℝ),(82876684962645303296/786981005458153:ℝ)],
  ![(91202631100818654084/786981005458153:ℝ),(178540887153422338816/786981005458153:ℝ),(87356505771436941312/786981005458153:ℝ)]
]
theorem admission09_04_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (30350348497062489/402934274794574336:ℝ) admission09_04_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 4 := by
 rw [admission09_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_04_coefficients]
def admission09_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(40318133174795716982692/491863128411345625:ℝ),(241780462736748968509636/1475589385234036875:ℝ),(24162016456319431011062/295117877046807375:ℝ)],
  ![(35069829782641255386726/491863128411345625:ℝ),(210493157686444184632012/1475589385234036875:ℝ),(105267255490708062384334/1475589385234036875:ℝ)]
]
theorem admission09_05_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (52604744673961883080089/1031511743474110300160000:ℝ) admission09_05_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 5 := by
 rw [admission09_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_05_coefficients]
def admission09_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(4307964378668576194090462490845863337472/206239921282991172178485579079197:ℝ),(12611732802202354893790894961947793661440/206239921282991172178485579079197:ℝ),(332504338617814392339639019629429243904/5574051926567328977796907542681:ℝ),(108077939849186658674511493383431127040/5574051926567328977796907542681:ℝ)],
  ![(4512730495543299836657217520669041026048/206239921282991172178485579079197:ℝ),(13220823495518213780620958549209833497600/206239921282991172178485579079197:ℝ),(12906598348375017882055318905676546342912/206239921282991172178485579079197:ℝ),(113472886279325670390676050733398753280/5574051926567328977796907542681:ℝ)]
]
theorem admission09_06_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (206142310808537785862944590346205/1902609724268314957754677774568448:ℝ) admission09_06_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 6 := by
 rw [admission09_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_06_coefficients]
def admission09_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(194883471957615549187393183712706614/506731993324302634345173412971:ℝ),(4220814802570063908800176507278984064/5574051926567328977796907542681:ℝ),(2077360080867328770378179115436113920/5574051926567328977796907542681:ℝ)],
  ![(2023442202237516757024992559423989436/5574051926567328977796907542681:ℝ),(3982215899627318544505694847670886656/5574051926567328977796907542681:ℝ),(1959029443349569536622460051898613760/5574051926567328977796907542681:ℝ)]
]
theorem admission09_07_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (119569668173191500037991946527015/475652431067078739438669443642112:ℝ) admission09_07_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 7 := by
 rw [admission09_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_07_coefficients]
def admission09_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(1556043496818273243962055712952030970665160339332272457/145157602254357525463461133923984375000000000000000:ℝ),(72758323600782888611597450440004722963318498845337344293/435472806763072576390383401771953125000000000000000:ℝ),(43766456393846246578435216301627558526436684992687043877/145157602254357525463461133923984375000000000000000:ℝ),(63205956489078681618344679072854213221724490275720604709/435472806763072576390383401771953125000000000000000:ℝ)],
  ![(687345967092136760479792144253628170967775708072026059/1199649605407913433582323420859375000000000000000:ℝ),(798219199583427650822322640187424487470681941004305400611/435472806763072576390383401771953125000000000000000:ℝ),(282592857579664810711623351215486391739593072827549100581/145157602254357525463461133923984375000000000000000:ℝ),(299062652612147139123050121602198102251616703258487360549/435472806763072576390383401771953125000000000000000:ℝ)]
]
theorem admission09_08_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1556043496818273243962055712952030970665160339332272457/25976964768676726889877200548774543360000000000000000000000:ℝ) admission09_08_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 8 := by
 rw [admission09_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_08_coefficients]
def admission09_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(95648326964635710991485587234625431001713891/36289400563589381365865283480996093750:ℝ),(835162119638996035189155848226428345430970789/108868201690768144097595850442988281250:ℝ),(404809197619942188825345172325879356152035648/54434100845384072048797925221494140625:ℝ),(2904465728892351681994133288720413536407552/1209646685452979378862176116033203125:ℝ)],
  ![(3323489944557332774181831262861677968123087/1649518207435880971175694703681640625:ℝ),(317356272580963720131667787659058288510284883/54434100845384072048797925221494140625:ℝ),(305742646964608471131264533992330869802447232/54434100845384072048797925221494140625:ℝ),(2179152911413913782094432195520825775650816/1209646685452979378862176116033203125:ℝ)]
]
theorem admission09_09_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (3192118522578975266739890911407459632301/317101620711385826292446295761408000000000:ℝ) admission09_09_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 9 := by
 rw [admission09_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_09_coefficients]
def admission09_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(870371221404131804696516173888/13833650486569095703125:ℝ),(12630552271973522478190116765376/69168252432845478515625:ℝ),(12207125624257038233421985922432/69168252432845478515625:ℝ),(436493071246470808746050002944/7685361381427275390625:ℝ)],
  ![(2584702146907439142823197454592/23056084144281826171875:ℝ),(7479499118018571284033295208192/23056084144281826171875:ℝ),(7205884369811923727376818052608/23056084144281826171875:ℝ),(770364333577347195388906766336/7685361381427275390625:ℝ)],
  ![(134849338214331827852640918784/2766730097313819140625:ℝ),(9715913286249706076521268554496/69168252432845478515625:ℝ),(9319507932975026642969888200192/69168252432845478515625:ℝ),(330537414693318473640515846144/7685361381427275390625:ℝ)]
]
theorem admission09_10_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (181569624770499649826943519/64469483967131893760000000000:ℝ) admission09_10_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 10 := by
 rw [admission09_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_10_coefficients]
def admission09_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(159854183583364764715935860659537226/506731993324302634345173412971:ℝ),(3462222498809655234010146497808349952/5574051926567328977796907542681:ℝ),(189342177854151528731705521677123584/619339102951925441977434171409:ℝ)],
  ![(1657340415664365215770755427572216388/5574051926567328977796907542681:ℝ),(3261786848576085488362756980304042496/5574051926567328977796907542681:ℝ),(178299061182778042309229898068631552/619339102951925441977434171409:ℝ)]
]
theorem admission09_11_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (65295066351115005728477745874743/317101620711385826292446295761408:ℝ) admission09_11_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 11 := by
 rw [admission09_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_11_coefficients]
def admission09_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission09_12_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission09_12_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 12 := by
 rw [admission09_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_12_coefficients]
def admission09_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(15975383012772521847/5000000000000000000000:ℝ)]
]
theorem admission09_13_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (15975383012772521847/5000000000000000000000:ℝ) admission09_13_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 13 := by
 rw [admission09_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_13_coefficients]
def admission09_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission09_14_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission09_14_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 14 := by
 rw [admission09_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_14_coefficients]
theorem admission09_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .weakC7 δ p j := by
 fin_cases j
 · exact admission09_00_pos hδ hp
 · exact admission09_01_pos hδ hp
 · exact admission09_02_pos hδ hp
 · exact admission09_03_pos hδ hp
 · exact admission09_04_pos hδ hp
 · exact admission09_05_pos hδ hp
 · exact admission09_06_pos hδ hp
 · exact admission09_07_pos hδ hp
 · exact admission09_08_pos hδ hp
 · exact admission09_09_pos hδ hp
 · exact admission09_10_pos hδ hp
 · exact admission09_11_pos hδ hp
 · exact admission09_12_pos hδ hp
 · exact admission09_13_pos hδ hp
 · exact admission09_14_pos hδ hp
#print axioms admission09_all
end
end RH20261023Finite
