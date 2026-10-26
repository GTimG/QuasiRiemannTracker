/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission30_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(34183749428474903/545478388005863:ℝ),(98914813121407120/1636435164017589:ℝ)]
]
theorem admission30_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (6182175820087945/6545740656070356:ℝ) admission30_00_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission30_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_00_coefficients]
def admission30_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(24910616832375232/545478388005863:ℝ),(72731850497125696/1636435164017589:ℝ)]
]
theorem admission30_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (1136435164017589/1636435164017589:ℝ) admission30_01_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission30_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_01_coefficients]
def admission30_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(12618356861625516/545478388005863:ℝ),(36887680273964128/1636435164017589:ℝ)]
]
theorem admission30_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (1152740008561379/3272870328035178:ℝ) admission30_02_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission30_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_02_coefficients]
def admission30_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(917174935338034478528/4909305492052767:ℝ),(5361211174876607043904/14727916476158301:ℝ),(2610424368862503608320/14727916476158301:ℝ)],
  ![(68699412149719511936/377638884004059:ℝ),(401299163374772920960/1132916652012177:ℝ),(2538368050032987006976/14727916476158301:ℝ)]
]
theorem admission30_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1239437524430169437/2513564411931016704:ℝ) admission30_03_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission30_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_03_coefficients]
def admission30_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(52730305392570498692/1636435164017589:ℝ),(101087278909264025408/1636435164017589:ℝ),(48396636519440935936/1636435164017589:ℝ)],
  ![(55196816170912241000/1636435164017589:ℝ),(105913633834828559488/1636435164017589:ℝ),(50757448056974640128/1636435164017589:ℝ)]
]
theorem admission30_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (47262340351016539/558569869318003712:ℝ) admission30_04_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission30_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_04_coefficients]
def admission30_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(9417813599868412166432/613663186506595875:ℝ),(94993669631748278112388/3068315932532979375:ℝ),(5318739514139424999192/340923992503664375:ℝ)],
  ![(7740592546717629081224/613663186506595875:ℝ),(78430487365889920056376/3068315932532979375:ℝ),(13230233965105807191752/1022771977510993125:ℝ)]
]
theorem admission30_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (967574068339703635153/26811353727264178176000:ℝ) admission30_05_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission30_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_05_coefficients]
def admission30_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(22125677920057098756132544783198216064/7021632876606929498129401237659:ℝ),(8060005791582889001589402865951655891072/891747375329080046262433957182693:ℝ),(7697173346676400946279009756822493016064/891747375329080046262433957182693:ℝ),(2447091079292648856988892078337010565120/891747375329080046262433957182693:ℝ)],
  ![(2927103387331892318700588742561282493696/891747375329080046262433957182693:ℝ),(8405653749886834301601685459240867622144/891747375329080046262433957182693:ℝ),(8037159302253309090303840521626112811008/891747375329080046262433957182693:ℝ),(69150552747799760682182913647203450880/24101280414299460709795512356289:ℝ)]
]
theorem admission30_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (18669823297825995307837616564460835/152191552056162994562122062025846272:ℝ) admission30_06_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission30_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_06_coefficients]
def admission30_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2168813876470337485308851632712632844/24101280414299460709795512356289:ℝ),(1403717939658967789108384464969095488/8033760138099820236598504118763:ℝ),(2043293280437571408607681467723161600/24101280414299460709795512356289:ℝ)],
  ![(2033290727762152932798635251382545208/24101280414299460709795512356289:ℝ),(1314769254303294870251183567249236096/8033760138099820236598504118763:ℝ),(1911938712409441818054330516226672640/24101280414299460709795512356289:ℝ)]
]
theorem admission30_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (933563824418672762721841072376305/4113285190707107961138434108806656:ℝ) admission30_07_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission30_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_07_coefficients]
def admission30_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(126018113714181855249354746086779311759583596741645775127/1506330025893716294362219522268062500000000000000000:ℝ),(2024133574881026728049837667625288614243717419921915689997/7531650129468581471811097611340312500000000000000000:ℝ),(2158438135461820147188731184988929527104811557597418340647/7531650129468581471811097611340312500000000000000000:ℝ),(152867223225703448856735639774742177226025536776746305257/1506330025893716294362219522268062500000000000000000:ℝ)],
  ![(47890802138709616654314225823044916262544664152541218641/301266005178743258872443904453612500000000000000000:ℝ),(3685563422241962934232297641050670579643163570127617774339/7531650129468581471811097611340312500000000000000000:ℝ),(3780378287244410104630081964205131010894314217732466263719/7531650129468581471811097611340312500000000000000000:ℝ),(19877299478538049572494446027449606100635013483359676237/115871540453362791874016886328312500000000000000000:ℝ)]
]
theorem admission30_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (126018113714181855249354746086779311759583596741645775127/33696032282272628417646052219344125952000000000000000000000:ℝ) admission30_08_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission30_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_08_coefficients]
def admission30_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(500077361542290682564659603466133561845511/2510550043156193823937032537113437500:ℝ),(175590876663864809271832423970738894712755867/313818755394524227992129067139179687500:ℝ),(4547852590546960409932993577671288113357872/8717187649847895222003585198310546875:ℝ),(506435886462345683470079312477844749425664/3138187553945242279921290671391796875:ℝ)],
  ![(3694083908781299930408826344316261505781539/31381875539452422799212906713917968750:ℝ),(50297586986359586023890877189803375862350367/156909377697262113996064533569589843750:ℝ),(2511455326101966270323241634152757413229024/8717187649847895222003585198310546875:ℝ),(1338010498860357035626606384337869557342976/15690937769726211399606453356958984375:ℝ)]
]
theorem admission30_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5226603511173269670416431188819802958371/1371095063569035987046144702935552000000000:ℝ) admission30_09_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission30_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_09_coefficients]
def admission30_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(670771352952870660563865137344/143827309337483408203125:ℝ),(41147880125417098342314997792/3196162429721853515625:ℝ),(1691582497600672951082261889248/143827309337483408203125:ℝ),(170239779370966395413984041984/47942436445827802734375:ℝ)],
  ![(1015930825414171543590758364928/143827309337483408203125:ℝ),(304961651500181166221137903744/15980812148609267578125:ℝ),(2442432547000322449314437172608/143827309337483408203125:ℝ),(374671745656358791031472128/75499899914689453125:ℝ)],
  ![(112234207596838615502468923648/47942436445827802734375:ℝ),(32154397361882283542274211712/5326937382869755859375:ℝ),(242183621383406886270339039872/47942436445827802734375:ℝ),(21678427053601649964113352704/15980812148609267578125:ℝ)]
]
theorem admission30_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (31755508379299291939619169/44685589545440296960000000000:ℝ) admission30_10_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission30_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_10_coefficients]
def admission30_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1781226103207035890761724534682836660/24101280414299460709795512356289:ℝ),(1153139213176684568692851337130218240/8033760138099820236598504118763:ℝ),(1679105491886293321647309634930196480/24101280414299460709795512356289:ℝ)],
  ![(1667496473343783812007624540069801032/24101280414299460709795512356289:ℝ),(1078509969831409046885211852964761088/8033760138099820236598504118763:ℝ),(1568914770498869057748455816713859072/24101280414299460709795512356289:ℝ)]
]
theorem admission30_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (383035832641325453551869095877407/2056642595353553980569217054403328:ℝ) admission30_11_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission30_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_11_coefficients]
def admission30_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission30_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission30_12_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission30_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_12_coefficients]
def admission30_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(45103798360955722411/10000000000000000000000:ℝ)]
]
theorem admission30_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (45103798360955722411/10000000000000000000000:ℝ) admission30_13_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission30_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_13_coefficients]
def admission30_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission30_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission30_14_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission30_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_14_coefficients]
theorem admission30_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .P δ p j := by
 fin_cases j
 · exact admission30_00_pos hδ hp
 · exact admission30_01_pos hδ hp
 · exact admission30_02_pos hδ hp
 · exact admission30_03_pos hδ hp
 · exact admission30_04_pos hδ hp
 · exact admission30_05_pos hδ hp
 · exact admission30_06_pos hδ hp
 · exact admission30_07_pos hδ hp
 · exact admission30_08_pos hδ hp
 · exact admission30_09_pos hδ hp
 · exact admission30_10_pos hδ hp
 · exact admission30_11_pos hδ hp
 · exact admission30_12_pos hδ hp
 · exact admission30_13_pos hδ hp
 · exact admission30_14_pos hδ hp
#print axioms admission30_all
end
end RH20261023Finite
