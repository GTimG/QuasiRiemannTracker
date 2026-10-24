/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission24_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(95703941878762633/786981005458153:ℝ),(93916960873304480/786981005458153:ℝ)]
]
theorem admission24_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission24_00_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission24_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_00_coefficients]
def admission24_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(69733568698643584/786981005458153:ℝ),(68733568698643584/786981005458153:ℝ)]
]
theorem admission24_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission24_01_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission24_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_01_coefficients]
def admission24_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(35451730827454582/786981005458153:ℝ),(34970600068684672/786981005458153:ℝ)]
]
theorem admission24_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission24_02_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission24_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_02_coefficients]
def admission24_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(20483595481451465611136/7082829049123377:ℝ),(13472596430075548226176/2360943016374459:ℝ),(19935624808775179067392/7082829049123377:ℝ)],
  ![(20346155476858497290240/7082829049123377:ℝ),(13381045559640806748160/2360943016374459:ℝ),(19798421202063922954240/7082829049123377:ℝ)]
]
theorem admission24_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (151049966446410545/302200706095930752:ℝ) admission24_03_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission24_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_03_coefficients]
def admission24_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(371953963512663967818/786981005458153:ℝ),(727738290020954774400/786981005458153:ℝ),(355860826298935222272/786981005458153:ℝ)],
  ![(376531415020913019328/786981005458153:ℝ),(736791497207236694016/786981005458153:ℝ),(360337063107726860288/786981005458153:ℝ)]
]
theorem admission24_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (130320126818457723/1611737099178297344:ℝ) admission24_04_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission24_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_04_coefficients]
def admission24_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(124711325750976636759006/491863128411345625:ℝ),(749982799305350329687864/1475589385234036875:ℝ),(375779886382462139992096/1475589385234036875:ℝ)],
  ![(23893052362389435032608/98372625682269125:ℝ),(13067435168273555378368/26828897913346125:ℝ),(72048755918314609464224/295117877046807375:ℝ)]
]
theorem admission24_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (2239973658974009534307/51575587173705515008000:ℝ) admission24_05_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission24_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_05_coefficients]
def admission24_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(6138060856185113908712078564906665328128/68746640427663724059495193026399:ℝ),(53936982582699802809891093541518377024000/206239921282991172178485579079197:ℝ),(52644363959639464808831759008264599781376/206239921282991172178485579079197:ℝ),(51416000435788409538857955439838494720/619339102951925441977434171409:ℝ)],
  ![(6206167714351718593238354833514391224320/68746640427663724059495193026399:ℝ),(54544733775566089401400612152780416860160/206239921282991172178485579079197:ℝ),(53246959472028177930210397195652264099840/206239921282991172178485579079197:ℝ),(52014092534474997814295404034279342080/619339102951925441977434171409:ℝ)]
]
theorem admission24_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (294204714407663781388423664702445/2536812965691086610339570366091264:ℝ) admission24_06_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission24_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_06_coefficients]
def admission24_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(7719248635527007139001062136935475158/5574051926567328977796907542681:ℝ),(1688157630470602105251707586858540672/619339102951925441977434171409:ℝ),(7475140720762466497321243016981954560/5574051926567328977796907542681:ℝ)],
  ![(7599066721901130724261166800519691840/5574051926567328977796907542681:ℝ),(1661667614370231906796235402457640960/619339102951925441977434171409:ℝ),(7356904751541267554481363953444454400/5574051926567328977796907542681:ℝ)]
]
theorem admission24_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (28064364439168043344426589788225/118913107766769684859667360910528:ℝ) admission24_07_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission24_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_07_coefficients]
def admission24_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(335741056558531964851186805537297730886181993212934933579/145157602254357525463461133923984375000000000000000:ℝ),(3169045776684593577602245931241718660101329692429545402911/435472806763072576390383401771953125000000000000000:ℝ),(3316322388817188393317536564086532930039708851762239803997/435472806763072576390383401771953125000000000000000:ℝ),(128276216256288498472146512526991840178349805371833244647/48385867418119175154487044641328125000000000000000:ℝ)],
  ![(418102067209050437700536659024220210076367693550317814261/145157602254357525463461133923984375000000000000000:ℝ),(3901230980726436916121614402678137737509943134588513459229/435472806763072576390383401771953125000000000000000:ℝ),(4039516408582638918363396688776497543759178015266825974109/435472806763072576390383401771953125000000000000000:ℝ),(14066441484505311053711592654214300568030711730598646037/4398715219829015923135185876484375000000000000000:ℝ)]
]
theorem admission24_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (335741056558531964851186805537297730886181993212934933579/103907859074706907559508802195098173440000000000000000000000:ℝ) admission24_08_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission24_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_08_coefficients]
def admission24_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(689651302720369601741895942739639497693794411/108868201690768144097595850442988281250:ℝ),(1991961150823186544615613352819838710826746783/108868201690768144097595850442988281250:ℝ),(319213150651720887806059085987420488523769152/18144700281794690682932641740498046875:ℝ),(61297193188149432627387629522360858382997504/10886820169076814409759585044298828125:ℝ)],
  ![(62194090099471116300258967573229020058477648/10886820169076814409759585044298828125:ℝ),(179116172088933593677433229866152694241634576/10886820169076814409759585044298828125:ℝ),(57226445622328591608043441308580865281447936/3628940056358938136586528348099609375:ℝ),(10951508858754691032762063936712913707237376/2177364033815362881951917008859765625:ℝ)]
]
theorem admission24_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (334213527183675873802553220724881399757/47565243106707873943866944364211200000000:ℝ) admission24_09_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission24_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_09_coefficients]
def admission24_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(40389233189982834084934824743744/69168252432845478515625:ℝ),(12849286152224464899480289777344/7685361381427275390625:ℝ),(2447454052916790671769186594688/1537072276285455078125:ℝ),(3171021935881344792656873955328/6288022948440498046875:ℝ)],
  ![(1695533879840515246780569432064/1537072276285455078125:ℝ),(1743808648174782937847814541312/553346019462763828125:ℝ),(41417220187543280118824792399872/13833650486569095703125:ℝ),(4360623239746114631218184585216/4611216828856365234375:ℝ)],
  ![(1435152593386129572460792446976/2766730097313819140625:ℝ),(371783981113277992139148034048/251520917937619921875:ℝ),(3874390798570284562350879408128/2766730097313819140625:ℝ),(1219925719710356221281043480576/2766730097313819140625:ℝ)]
]
theorem admission24_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (290852956702794127769719/161173709917829734400000000:ℝ) admission24_10_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission24_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_10_coefficients]
def admission24_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(6327806738567536110481700007415727018/5574051926567328977796907542681:ℝ),(12455135599894173162227162198497444096/5574051926567328977796907542681:ℝ),(6128257043440737372246266493041451008/5574051926567328977796907542681:ℝ)],
  ![(6226742890166115885088611842733033920/5574051926567328977796907542681:ℝ),(12254684835548667027491436680993136640/5574051926567328977796907542681:ℝ),(6028862122257688052627153880565022720/5574051926567328977796907542681:ℝ)]
]
theorem admission24_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (45996567705213074131982070011635/237826215533539369719334721821056:ℝ) admission24_11_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission24_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_11_coefficients]
def admission24_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission24_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission24_12_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission24_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_12_coefficients]
def admission24_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission24_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission24_13_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission24_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_13_coefficients]
def admission24_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission24_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission24_14_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission24_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_14_coefficients]
theorem admission24_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission24_00_pos hδ hp
 · exact admission24_01_pos hδ hp
 · exact admission24_02_pos hδ hp
 · exact admission24_03_pos hδ hp
 · exact admission24_04_pos hδ hp
 · exact admission24_05_pos hδ hp
 · exact admission24_06_pos hδ hp
 · exact admission24_07_pos hδ hp
 · exact admission24_08_pos hδ hp
 · exact admission24_09_pos hδ hp
 · exact admission24_10_pos hδ hp
 · exact admission24_11_pos hδ hp
 · exact admission24_12_pos hδ hp
 · exact admission24_13_pos hδ hp
 · exact admission24_14_pos hδ hp
#print axioms admission24_all
end
end RH20261023Finite
