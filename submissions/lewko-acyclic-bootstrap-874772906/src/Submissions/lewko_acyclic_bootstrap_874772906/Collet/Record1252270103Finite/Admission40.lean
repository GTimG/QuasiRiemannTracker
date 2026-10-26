/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission40_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(42988324622372947/22486655455827:ℝ), (300560865768419840/157406588190789:ℝ)]]
theorem admission40_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission40_00_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission40_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_00_coefficients]
def admission40_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(31452670373533696/22486655455827:ℝ), (219968692614735872/157406588190789:ℝ)]]
theorem admission40_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission40_01_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission40_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_01_coefficients]
def admission40_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(5333942036242054/7495551818609:ℝ), (37305518869776384/52468862730263:ℝ)]]
theorem admission40_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission40_02_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission40_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_02_coefficients]
def admission40_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1175652034330246759942144/202379899102443:ℝ), (783100733118502644635648/67459966367481:ℝ), (8215553406976828217753600/1416659293717101:ℝ)],
![(8222538044216548634828800/1416659293717101:ℝ), (5477021261593321545064448/472219764572367:ℝ), (8208527994163416000364544/1416659293717101:ℝ)]]
theorem admission40_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1957065580883840561/3868424311376830464:ℝ) admission40_03_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission40_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_03_coefficients]
def admission40_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(47923732875762048806334/52468862730263:ℝ), (95712957754093189933056/52468862730263:ℝ), (47789265004636422537216/52468862730263:ℝ)],
![(48000242066713606337384/52468862730263:ℝ), (13695124087944952225792/7495551818609:ℝ), (6837952386754532081664/7495551818609:ℝ)]]
theorem admission40_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (68363091952280649/859649846972628992:ℝ) admission40_04_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission40_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_04_coefficients]
def admission40_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(10607290980447616639190746/19675823523848625:ℝ), (318245780654141670383921576/295137352857729375:ℝ), (159136307471297712862031636/295137352857729375:ℝ)],
![(52771066391135499400021412/98379117619243125:ℝ), (316654095075567356023343144/295137352857729375:ℝ), (158340787339319615350533908/295137352857729375:ℝ)]]
theorem admission40_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (13192766597783874850005353/281690061855991068098560000:ℝ) admission40_05_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission40_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_05_coefficients]
def admission40_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(600175763103485422493192382775322800922624/222991506052781715650379982689:ℝ), (2463541543111579548527987596476505255272448/305580952738997165891261457759:ℝ), (66411798671812001628419167081871331597221888/8250685723952923479064059359493:ℝ), (22102680231361000276379358756892633339002880/8250685723952923479064059359493:ℝ)],
![(22239193313967964997150442077011088716169216/8250685723952923479064059359493:ℝ), (2467171836493007131692801752200822829121536/305580952738997165891261457759:ℝ), (66509764311693756713691323437404147465322496/8250685723952923479064059359493:ℝ), (22135318029074208335081448939393019795210240/8250685723952923479064059359493:ℝ)]]
theorem admission40_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (10292362529486883560372217910779935/90119489934163132187323699030622208:ℝ) admission40_06_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission40_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_06_coefficients]
def admission40_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(69135999527132429858365111552424854366/24776834005864635072264442521:ℝ), (414392102124946269022813610419003430912/74330502017593905216793327563:ℝ), (7666081824172758858036460127571148800/2752981556207181674696049169:ℝ)],
![(1408190014307898098439854679011896168/505649673589074185148253929:ℝ), (8440497610289913012724922773956141056/1516949020767222555444761787:ℝ), (156145545281091946404209588730593280/56183297065452687238694881:ℝ)]]
theorem admission40_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (55841998558434944058970065855/230126784780094206929694232576:ℝ) admission40_07_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission40_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_07_coefficients]
def admission40_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1392646179714997739395613457081424714408826779666440118649/24196126958852182687758244649414062500000000000:ℝ), (4197343734443306715612979848989495909893828260110673844967/24196126958852182687758244649414062500000000000:ℝ), (37950719345339708411792195291544557857674850385764281763901/217765142629669644189824201844726562500000000000:ℝ), (12708441298351412566497151984554811815892880799852115727039/217765142629669644189824201844726562500000000000:ℝ)],
![(1446957920775251169219797269987300161893589263271188666207/24196126958852182687758244649414062500000000000:ℝ), (4360151967565187003230309065914251894332288211139651170541/24196126958852182687758244649414062500000000000:ℝ), (1576594044506929200404178749623016726799714509839354932677/8710605705186785767592968073789062500000000000:ℝ), (1885157805298111491746514601779979760368588626385565825417/31109306089952806312832028834960937500000000000:ℝ)]]
theorem admission40_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1392646179714997739395613457081424714408826779666440118649/567550356019249492471202012220622897152000000000000000000000:ℝ) admission40_08_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission40_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_08_coefficients]
def admission40_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(442592733797897271249481128587071840848465574198/2177651426296696441898242018447265625:ℝ), (441467043528781353476470185763727151045727810888/725883808765565480632747339482421875:ℝ), (1321024995352953489833900533451029023138445705216/2177651426296696441898242018447265625:ℝ), (3513732792136756121069674364905757997241729024/17421211410373571535185936147578125:ℝ)],
![(437222904687307835371026100817387317263606503176/2177651426296696441898242018447265625:ℝ), (436101137406621059540977482257541632499251672416/725883808765565480632747339482421875:ℝ), (1304939040245676603142987889810502838156479496192/2177651426296696441898242018447265625:ℝ), (86771706633214171039548397494411648576388071424/435530285259339288379648403689453125:ℝ)]]
theorem admission40_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5171996750427137079211973994637229953789/608915472528129271535970939396096000000000:ℝ) admission40_09_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission40_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_09_coefficients]
def admission40_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2041128122508989809443961884929936384/13834563415206064453125:ℝ), (2034774717744703100376584502964487168/4611521138402021484375:ℝ), (2028422598925429521017792095479037952/4611521138402021484375:ℝ), (2022071767921834329180084662473588736/13834563415206064453125:ℝ)],
![(4054706604545064090299161193608978432/13834563415206064453125:ℝ), (192476962234893438417731083222704128/219596244685810546875:ℝ), (12087985120339604190554974658193784832/13834563415206064453125:ℝ), (17851747145914234880164789372321792/61486948512026953125:ℝ)],
![(80542155249480186515507930657767424/553382536608242578125:ℝ), (2007216905567708236835778512835198976/4611521138402021484375:ℝ), (6002643624217335605732291089838637056/13834563415206064453125:ℝ), (1994546790624872683112653817777225728/13834563415206064453125:ℝ)]]
theorem admission40_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (7430265808943184774788669563/3301055412374895329280000000000:ℝ) admission40_10_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission40_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_10_coefficients]
def admission40_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(56697984126900262267620383379003987106/24776834005864635072264442521:ℝ), (37760138862039902620661421070836494336/8258944668621545024088147507:ℝ), (169747398627995349375674620034185953280/74330502017593905216793327563:ℝ)],
![(1154790954931122606826197712611685528/505649673589074185148253929:ℝ), (1794509208049714406986840688682483712/393283079458168810670864167:ℝ), (24201153012874037009964635263137218560/10618643145370557888113332509:ℝ)]]
theorem admission40_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (5770004513948926212779196563515/28995974882291870073141473304576:ℝ) admission40_11_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission40_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_11_coefficients]
def admission40_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission40_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission40_12_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission40_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_12_coefficients]
def admission40_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission40_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission40_13_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission40_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_13_coefficients]
def admission40_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission40_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission40_14_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission40_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_14_coefficients]
theorem admission40_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission40_00_pos hδ hp
 · exact admission40_01_pos hδ hp
 · exact admission40_02_pos hδ hp
 · exact admission40_03_pos hδ hp
 · exact admission40_04_pos hδ hp
 · exact admission40_05_pos hδ hp
 · exact admission40_06_pos hδ hp
 · exact admission40_07_pos hδ hp
 · exact admission40_08_pos hδ hp
 · exact admission40_09_pos hδ hp
 · exact admission40_10_pos hδ hp
 · exact admission40_11_pos hδ hp
 · exact admission40_12_pos hδ hp
 · exact admission40_13_pos hδ hp
 · exact admission40_14_pos hδ hp
#print axioms admission40_all
end
end Record1252270103Finite
