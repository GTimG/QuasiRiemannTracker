/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission31_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(201466061406831829/1636435164017589:ℝ),(197829626242814240/1636435164017589:ℝ)]
]
theorem admission31_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (6182175820087945/6545740656070356:ℝ) admission31_00_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission31_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_00_coefficients]
def admission31_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(147463700994251392/1636435164017589:ℝ),(145463700994251392/1636435164017589:ℝ)]
]
theorem admission31_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (1136435164017589/1636435164017589:ℝ) admission31_01_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission31_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_01_coefficients]
def admission31_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(74742750858840676/1636435164017589:ℝ),(73775360547928256/1636435164017589:ℝ)]
]
theorem admission31_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (1152740008561379/3272870328035178:ℝ) admission31_02_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission31_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_02_coefficients]
def admission31_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(10723160349753214087808/14727916476158301:ℝ),(2351568869467025391232/1636435164017589:ℝ),(10441697475450014433280/14727916476158301:ℝ)],
  ![(10434534247744095944960/14727916476158301:ℝ),(2287472271986227108096/1636435164017589:ℝ),(10153472200131948027904/14727916476158301:ℝ)]
]
theorem admission31_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1239437524430169437/2513564411931016704:ℝ) admission31_03_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission31_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_03_coefficients]
def admission31_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(202214220821275460036/1636435164017589:ℝ),(395761103896291794560/1636435164017589:ℝ),(193586546077763743744/1636435164017589:ℝ)],
  ![(211867898062715440616/1636435164017589:ℝ),(414857059897555679488/1636435164017589:ℝ),(203029792227898560512/1636435164017589:ℝ)]
]
theorem admission31_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (47262340351016539/558569869318003712:ℝ) admission31_04_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission31_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_04_coefficients]
def admission31_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(4198783171736082471792/68184798500732875:ℝ),(379449660712072950782416/3068315932532979375:ℝ),(190468471978797847264276/3068315932532979375:ℝ)],
  ![(17313111273841559370124/340923992503664375:ℝ),(313611481252606621000504/3068315932532979375:ℝ),(157756657051048233594388/3068315932532979375:ℝ)]
]
theorem admission31_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (12984833455381169527593/357484716363522375680000:ℝ) admission31_05_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission31_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_05_coefficients]
def admission31_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(21014231313399190346886137888577332912384/891747375329080046262433957182693:ℝ),(2281157460949158330749192489970938786560/33027680567743705417127183599359:ℝ),(60153786338217390068982743967334098845696/891747375329080046262433957182693:ℝ),(19576728634341190855911136626696084520960/891747375329080046262433957182693:ℝ)],
  ![(21928486891140626855846882528374790609408/891747375329080046262433957182693:ℝ),(2381902496992535253180123697580198243840/33027680567743705417127183599359:ℝ),(62851482629036330104104575745862783434752/891747375329080046262433957182693:ℝ),(553204421982398085457463309177627607040/24101280414299460709795512356289:ℝ)]
]
theorem admission31_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (18669823297825995307837616564460835/152191552056162994562122062025846272:ℝ) admission31_06_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission31_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_06_coefficients]
def admission31_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(8423260975884812261241686495343080908/24101280414299460709795512356289:ℝ),(16595480759704092369081032660707219328/24101280414299460709795512356289:ℝ),(8173173121750285634430725870892646400/24101280414299460709795512356289:ℝ)],
  ![(7889537203081479361606516469356926136/24101280414299460709795512356289:ℝ),(15536370375457536493724423468402107136/24101280414299460709795512356289:ℝ),(7647754849637767272217322064906690560/24101280414299460709795512356289:ℝ)]
]
theorem admission31_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (933563824418672762721841072376305/4113285190707107961138434108806656:ℝ) admission31_07_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission31_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_07_coefficients]
def admission31_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(98312249477866181534659357642527759783888134396084494793/139475002397566323552057363172968750000000000000000:ℝ),(2743937603111323121977403810128763496641266835061283126511/1255275021578096911968516268556718750000000000000000:ℝ),(8500687582838494370733408359382134534070466136913128268391/3765825064734290735905548805670156250000000000000000:ℝ),(2923276002895319180686005060882180265547203041673560248269/3765825064734290735905548805670156250000000000000000:ℝ)],
  ![(179390727885584946009906643951681895105476942229060402699/139475002397566323552057363172968750000000000000000:ℝ),(4906729336729817806927585113658538651378565517754529865793/1255275021578096911968516268556718750000000000000000:ℝ),(2982139597252482030637374935055523712823272122478221737851/753165012946858147181109761134031250000000000000000:ℝ),(29787156229592562676922178890675942646105300661610354821/22282988548723613821926324293906250000000000000000:ℝ)]
]
theorem admission31_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (98312249477866181534659357642527759783888134396084494793/24960023912794539568626705347662315520000000000000000000000:ℝ) admission31_08_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission31_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_08_coefficients]
def admission31_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(226233414381288143848505287223978218483447267/156909377697262113996064533569589843750:ℝ),(50382079163226897217540904254340389515555527/12069952130558624153543425659199218750:ℝ),(105217819732798093266203854179839932302860864/26151562949543685666010755594931640625:ℝ),(4051487091698765467760634499822757995405312/3138187553945242279921290671391796875:ℝ)],
  ![(63677153694352524449009711084756506201405127/78454688848631056998032266784794921875:ℝ),(180850293691841082824325767549438729458884511/78454688848631056998032266784794921875:ℝ),(56897673890430735956411027296590480105607808/26151562949543685666010755594931640625:ℝ),(10704083990882856285012851074702956458743808/15690937769726211399606453356958984375:ℝ)]
]
theorem admission31_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5226603511173269670416431188819802958371/1371095063569035987046144702935552000000000:ℝ) admission31_09_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission31_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_09_coefficients]
def admission31_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1574909264770070741097418017728/47942436445827802734375:ℝ),(13533955230367625772589110113984/143827309337483408203125:ℝ),(991920157519806310710190236032/11063639179806416015625:ℝ),(1361918234967731163311872335872/47942436445827802734375:ℝ)],
  ![(2305589303797162661936797025024/47942436445827802734375:ℝ),(19541537967856731770727957380864/143827309337483408203125:ℝ),(1410363561054280904633630887424/11063639179806416015625:ℝ),(2997373965250870328251777024/75499899914689453125:ℝ)],
  ![(47256179093199400236374395136/3196162429721853515625:ℝ),(1937725325012338348196332318976/47942436445827802734375:ℝ),(1749157859463286943789436856832/47942436445827802734375:ℝ),(173427416428813199712906821632/15980812148609267578125:ℝ)]
]
theorem admission31_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (31755508379299291939619169/44685589545440296960000000000:ℝ) admission31_10_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission31_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_10_coefficients]
def admission31_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(6919749234623382918487588181003687860/24101280414299460709795512356289:ℝ),(13635257246605280698746346562502095360/24101280414299460709795512356289:ℝ),(6716421967545173286589238539720785920/24101280414299460709795512356289:ℝ)],
  ![(6471941153336880010411715915677943368/24101280414299460709795512356289:ℝ),(12746718900983930512305094384644002816/24101280414299460709795512356289:ℝ),(6275659081995476230993823266855436288/24101280414299460709795512356289:ℝ)]
]
theorem admission31_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (383035832641325453551869095877407/2056642595353553980569217054403328:ℝ) admission31_11_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission31_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_11_coefficients]
def admission31_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission31_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission31_12_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission31_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_12_coefficients]
def admission31_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(45103798360955722411/10000000000000000000000:ℝ)]
]
theorem admission31_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (45103798360955722411/10000000000000000000000:ℝ) admission31_13_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission31_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_13_coefficients]
def admission31_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission31_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission31_14_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission31_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_14_coefficients]
theorem admission31_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .P δ p j := by
 fin_cases j
 · exact admission31_00_pos hδ hp
 · exact admission31_01_pos hδ hp
 · exact admission31_02_pos hδ hp
 · exact admission31_03_pos hδ hp
 · exact admission31_04_pos hδ hp
 · exact admission31_05_pos hδ hp
 · exact admission31_06_pos hδ hp
 · exact admission31_07_pos hδ hp
 · exact admission31_08_pos hδ hp
 · exact admission31_09_pos hδ hp
 · exact admission31_10_pos hδ hp
 · exact admission31_11_pos hδ hp
 · exact admission31_12_pos hδ hp
 · exact admission31_13_pos hδ hp
 · exact admission31_14_pos hδ hp
#print axioms admission31_all
end
end RH20261023Finite
