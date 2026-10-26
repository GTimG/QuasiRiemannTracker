/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission19_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(48745461442110393/786981005458153:ℝ),(46958480436652240/786981005458153:ℝ)]
]
theorem admission19_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission19_00_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission19_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_00_coefficients]
def admission19_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(35366784349321792/786981005458153:ℝ),(34366784349321792/786981005458153:ℝ)]
]
theorem admission19_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission19_01_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission19_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_01_coefficients]
def admission19_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(17966430793112246/786981005458153:ℝ),(17485300034342336/786981005458153:ℝ)]
]
theorem admission19_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission19_02_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission19_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_02_coefficients]
def admission19_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(446820903365662369600/2360943016374459:ℝ),(2611813936903796321728/7082829049123377:ℝ),(1271702226806809212928/7082829049123377:ℝ)],
  ![(39577215438736878080/214631183306769:ℝ),(2543089434607312161280/7082829049123377:ℝ),(1237401325128995184640/7082829049123377:ℝ)]
]
theorem admission19_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (151049966446410545/302200706095930752:ℝ) admission19_03_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission19_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_03_coefficients]
def admission19_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(23804723132074811706/786981005458153:ℝ),(45607613475342020544/786981005458153:ℝ),(21821654442859235328/786981005458153:ℝ)],
  ![(24974630249380812912/786981005458153:ℝ),(47896098664087161344/786981005458153:ℝ),(22940713645057144832/786981005458153:ℝ)]
]
theorem admission19_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (31965314125282083/402934274794574336:ℝ) admission19_04_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission19_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_04_coefficients]
def admission19_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1052917487412192619606/59023575409361475:ℝ),(4800108568257181786724/134144489566730625:ℝ),(8820449438763044831688/491863128411345625:ℝ)],
  ![(4467530239129309894664/295117877046807375:ℝ),(8986463024224230810128/295117877046807375:ℝ),(1505154774571124088488/98372625682269125:ℝ)]
]
theorem admission19_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (558441279891163736833/12893896793426378752000:ℝ) admission19_05_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission19_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_05_coefficients]
def admission19_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(606334951679824607045089057393164936448/206239921282991172178485579079197:ℝ),(578926559916471239179613060543246345984/68746640427663724059495193026399:ℝ),(150560492725112464069038754443503939584/18749083752999197470771416279927:ℝ),(1578714446492453972678180704630538240/619339102951925441977434171409:ℝ)],
  ![(632533224235844408248734306688638515200/206239921282991172178485579079197:ℝ),(604681423603896054499843595599242536960/68746640427663724059495193026399:ℝ),(1732127547249927674208834452494658600960/206239921282991172178485579079197:ℝ),(1653475958828277507107861778935644160/619339102951925441977434171409:ℝ)]
]
theorem admission19_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (72267812186849394501259492704645/634203241422771652584892591522816:ℝ) admission19_06_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission19_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_06_coefficients]
def admission19_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(57859221639956807274983599105718326/619339102951925441977434171409:ℝ),(1009850060064918872465279631619587904/5574051926567328977796907542681:ℝ),(489365539276628957865055012974653440/5574051926567328977796907542681:ℝ)],
  ![(54466351253344556452734679939483920/619339102951925441977434171409:ℝ),(949762972223852450835594333584289280/5574051926567328977796907542681:ℝ),(459806546971329222155085247090278400/5574051926567328977796907542681:ℝ)]
]
theorem admission19_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (28064364439168043344426589788225/118913107766769684859667360910528:ℝ) admission19_07_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission19_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_07_coefficients]
def admission19_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(6864531854500898949795457363012460754866981510911715717/174189122705229030556153360708781250000000000000000:ℝ),(41621108272591762443777147674711568456890192152267483213/290315204508715050926922267847968750000000000000000:ℝ),(146689408125207492870930597795986890088984391912498025909/870945613526145152780766803543906250000000000000000:ℝ),(11228391070547906757685690753011941374808238352050830971/174189122705229030556153360708781250000000000000000:ℝ)],
  ![(19675517770327985766321146727817621941819439185297840491/174189122705229030556153360708781250000000000000000:ℝ),(4165644394516534424745821130517414200429786864643458703/11612608180348602037076890713918750000000000000000:ℝ),(65943519502672154868552773024550460195259962785543208817/174189122705229030556153360708781250000000000000000:ℝ),(23132979103519372161092143754226401106302849001189168763/174189122705229030556153360708781250000000000000000:ℝ)]
]
theorem admission19_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (6864531854500898949795457363012460754866981510911715717/3896544715301509033481580082316181504000000000000000000000:ℝ) admission19_08_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission19_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_08_coefficients]
def admission19_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(12214149015381104327281412379731668339762291/43547280676307257639038340177195312500:ℝ),(172623745006897635788461215539895781560881191/217736403381536288195191700885976562500:ℝ),(13510348037110079034892864170255915941549008/18144700281794690682932641740498046875:ℝ),(2528629370977417656816236219960928997607168/10886820169076814409759585044298828125:ℝ)],
  ![(2177786308757270318024660915285687707930738/10886820169076814409759585044298828125:ℝ),(6063124180284738778270080712885440599928866/10886820169076814409759585044298828125:ℝ),(169589053837737863784876599243173755757696/329903641487176194235138940736328125:ℝ),(342234651836084094773814498022278553351168/2177364033815362881951917008859765625:ℝ)]
]
theorem admission19_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (334213527183675873802553220724881399757/47565243106707873943866944364211200000000:ℝ) admission19_09_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission19_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_09_coefficients]
def admission19_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(8446607443711740978363180736/1257604589688099609375:ℝ),(433658059994163708145678746592/23056084144281826171875:ℝ),(134314565594335422844475017568/7685361381427275390625:ℝ),(372429410122235934973213858816/69168252432845478515625:ℝ)],
  ![(158227633449199581563453606912/13833650486569095703125:ℝ),(146377861679833223710729150976/4611216828856365234375:ℝ),(80758112076876719376538817024/2766730097313819140625:ℝ),(40962779389694502437986746368/4611216828856365234375:ℝ)],
  ![(1433664457929702976549081088/307414455257091015625:ℝ),(356747879879589809703450624/27946768659735546875:ℝ),(31945347171949222350458034176/2766730097313819140625:ℝ),(9530669685237157978758152192/2766730097313819140625:ℝ)]
]
theorem admission19_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (290852956702794127769719/161173709917829734400000000:ℝ) admission19_10_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission19_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_10_coefficients]
def admission19_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(427341197263480584054924052144076762/5574051926567328977796907542681:ℝ),(828755760742600779416341802567453824/5574051926567328977796907542681:ℝ),(401652612936867833193975270654420992/5574051926567328977796907542681:ℝ)],
  ![(401654000739051096124920493094430320/5574051926567328977796907542681:ℝ),(778227839161372371858035350053514240/5574051926567328977796907542681:ℝ),(376803882641105503289197117535313920/5574051926567328977796907542681:ℝ)]
]
theorem admission19_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (45996567705213074131982070011635/237826215533539369719334721821056:ℝ) admission19_11_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission19_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_11_coefficients]
def admission19_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission19_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission19_12_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission19_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_12_coefficients]
def admission19_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission19_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission19_13_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission19_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_13_coefficients]
def admission19_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission19_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission19_14_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission19_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_14_coefficients]
theorem admission19_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission19_00_pos hδ hp
 · exact admission19_01_pos hδ hp
 · exact admission19_02_pos hδ hp
 · exact admission19_03_pos hδ hp
 · exact admission19_04_pos hδ hp
 · exact admission19_05_pos hδ hp
 · exact admission19_06_pos hδ hp
 · exact admission19_07_pos hδ hp
 · exact admission19_08_pos hδ hp
 · exact admission19_09_pos hδ hp
 · exact admission19_10_pos hδ hp
 · exact admission19_11_pos hδ hp
 · exact admission19_12_pos hδ hp
 · exact admission19_13_pos hδ hp
 · exact admission19_14_pos hδ hp
#print axioms admission19_all
end
end RH20261023Finite
