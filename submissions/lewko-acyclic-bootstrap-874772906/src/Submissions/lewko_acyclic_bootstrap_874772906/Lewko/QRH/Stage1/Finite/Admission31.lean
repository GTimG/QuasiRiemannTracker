/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission31_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20146665261777203/163643883613523:ℝ),(19783021378163680/163643883613523:ℝ)]]
theorem admission31_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (618219418067615/654575534454092:ℝ) admission31_00_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission31_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_00_coefficients]
def admission31_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(14746417102530944/163643883613523:ℝ),(14546417102530944/163643883613523:ℝ)]]
theorem admission31_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (113643883613523/163643883613523:ℝ) admission31_01_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission31_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_01_coefficients]
def admission31_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7474298587436970/163643883613523:ℝ),(7377559556345728/163643883613523:ℝ)]]
theorem admission31_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (57637184033951/163643883613523:ℝ) admission31_02_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission31_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_02_coefficients]
def admission31_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1072319271092152963456/1472794952521707:ℝ),(705472802442617401472/490931650840569:ℝ),(1044172936235699240960/1472794952521707:ℝ)],
![(1043456580092902270720/1472794952521707:ℝ),(686243769191809346816/490931650840569:ℝ),(1015350327482525769728/1472794952521707:ℝ)]]
theorem admission31_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (123944131772769259/251357005230371328:ℝ) admission31_03_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission31_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_03_coefficients]
def admission31_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(20221485677329699898/163643883613523:ℝ),(39576235652906149248/163643883613523:ℝ),(19358716275851190272/163643883613523:ℝ)],
![(21186856456675575268/163643883613523:ℝ),(41485837316433186560/163643883613523:ℝ),(20303043899063443456/163643883613523:ℝ)]]
theorem admission31_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (7089373636175973/83785668410123776:ℝ) admission31_04_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission31_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_04_coefficients]
def admission31_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1259638462500068266232/20455485451690375:ℝ),(37945072544825270837012/306832281775355625:ℝ),(19046901006809107614782/306832281775355625:ℝ)],
![(5193947625359672828054/102277427258451875:ℝ),(31361234794851492840428/306832281775355625:ℝ),(32934675668213025154/640568437944375:ℝ)]]
theorem admission31_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (7790921438039509242081/214491311129916866560000:ℝ) admission31_05_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission31_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_05_coefficients]
def admission31_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(210143516983265304671750611374857153024/8917513774490715058197481019157:ℝ),(615916053466447311724387375176039475712/8917513774490715058197481019157:ℝ),(601541330317423730068223373293157203968/8917513774490715058197481019157:ℝ),(195768418117381173523623009491974881280/8917513774490715058197481019157:ℝ)],
![(219286134580178182602722498007493035008/8917513774490715058197481019157:ℝ),(643117397596025142373441178682377913344/8917513774490715058197481019157:ℝ),(628518476569291158642857222357781938176/8917513774490715058197481019157:ℝ),(204686828672757782319395341682897059840/8917513774490715058197481019157:ℝ)]]
theorem admission31_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (373398624644052836463209170326185/3043844701692830739864740187872256:ℝ) admission31_06_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission31_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_06_coefficients]
def admission31_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(84233122048211975921654755797935554/241013885797046352924256243761:ℝ),(165955822975518438431552171387229568/241013885797046352924256243761:ℝ),(81732234316243443257447277545062400/241013885797046352924256243761:ℝ)],
![(78895851672893101138791937333754548/241013885797046352924256243761:ℝ),(155364654144025152410866446126313216/241013885797046352924256243761:ℝ),(76478019253056364762325666845736960/241013885797046352924256243761:ℝ)]]
theorem admission31_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (4667847854800803513325541189315/20566518254681288782869866134272:ℝ) admission31_07_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission31_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_07_coefficients]
def admission31_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(884861258700883400401121659808962853055321225529116391/1255280655192949754813834602921875000000000000000:ℝ),(8232268800703913025462675723802683740226216238719353419/3765841965578849264441503808765625000000000000000:ℝ),(8501140471384700455234952671367439736284402292897945313/3765841965578849264441503808765625000000000000000:ℝ),(2923425940175836861499428933030135178862277855765941067/3765841965578849264441503808765625000000000000000:ℝ)],
![(1614570173563421216027928384157185021738935422420299013/1255280655192949754813834602921875000000000000000:ℝ),(14720667126359830750757643600176096402813089057039397797/3765841965578849264441503808765625000000000000000:ℝ),(2982234728800252813843973385079960718880349947778402093/753168393115769852888300761753125000000000000000:ℝ),(5034186812050740080741107361929813627361598199113509707/3765841965578849264441503808765625000000000000000:ℝ)]]
theorem admission31_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (884861258700883400401121659808962853055321225529116391/224641223389798823612359924495941632000000000000000000000:ℝ) admission31_08_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission31_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_08_coefficients]
def admission31_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2262332785702526501911247517586929656195383/1569100818991187193517293253652343750:ℝ),(19648995090842067097134281108118604688623297/4707302456973561580551879760957031250:ℝ),(9469594112118281907018647213231433740431424/2353651228486780790275939880478515625:ℝ),(40514820122655003112528393230392253145088/31382016379823743870345865073046875:ℝ)],
![(636768414319785823149677905984698077824523/784550409495593596758646626826171875:ℝ),(5425479172236170058579873705929263024626317/2353651228486780790275939880478515625:ℝ),(5120759482869177658741600550791559570112128/2353651228486780790275939880478515625:ℝ),(107040113468466060135176826760978101409792/156910081899118719351729325365234375:ℝ)]]
theorem admission31_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (52265680404524443425379309941883838579/13711012169787525855246577422848000000000:ℝ) admission31_09_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission31_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_09_coefficients]
def admission31_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(472475091542599511126257354688/14382763208219794921875:ℝ),(1353402269580305080518292660288/14382763208219794921875:ℝ),(1289502760236847749181418256512/14382763208219794921875:ℝ),(136192530506484893263127650304/4794254402739931640625:ℝ)],
![(691680588594225667841995944704/14382763208219794921875:ℝ),(1954164827009264156343330696448/14382763208219794921875:ℝ),(1833483294827003823113893558784/14382763208219794921875:ℝ),(38066878204547688974170587136/958850880547986328125:ℝ)],
![(14176951263669886259996006656/958850880547986328125:ℝ),(193773938266164995862531826432/4794254402739931640625:ℝ),(174917133995692348362463553024/4794254402739931640625:ℝ),(17342884963875594599970586624/1598084800913310546875:ℝ)]]
theorem admission31_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (9526731242363302697737749/13405706945619804160000000000:ℝ) admission31_10_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission31_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_10_coefficients]
def admission31_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(69197899894452027973071007233435838/241013885797046352924256243761:ℝ),(136353381496887947368147037253165824/241013885797046352924256243761:ℝ),(7462735685201318880502179109765120/26779320644116261436028471529:ℝ)],
![(64719792861912968633936568954894412/241013885797046352924256243761:ℝ),(127467945809384453675183051485498880/241013885797046352924256243761:ℝ),(6972996255484185557265418711261184/26779320644116261436028471529:ℝ)]]
theorem admission31_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2553587495904853109350128922581/13711012169787525855246577422848:ℝ) admission31_11_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission31_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_11_coefficients]
def admission31_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission31_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission31_12_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission31_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_12_coefficients]
def admission31_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4510254983728566477/1000000000000000000000:ℝ)]]
theorem admission31_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4510254983728566477/1000000000000000000000:ℝ) admission31_13_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission31_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_13_coefficients]
def admission31_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission31_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission31_14_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_14_coefficients,Fin.sum_univ_succ] <;> ring
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
end LewkoStage1Finite
