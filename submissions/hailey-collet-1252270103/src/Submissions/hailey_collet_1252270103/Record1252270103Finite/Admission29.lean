/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission29_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19142460698717029/157406588190789:ℝ), (18785054110526240/157406588190789:ℝ)]]
theorem admission29_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission29_00_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission29_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_00_coefficients]
def admission29_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(13948043288420992/157406588190789:ℝ), (13748043288420992/157406588190789:ℝ)]]
theorem admission29_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission29_01_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission29_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_01_coefficients]
def admission29_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2363670313279018/52468862730263:ℝ), (2331594929361024/52468862730263:ℝ)]]
theorem admission29_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission29_02_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission29_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_02_coefficients]
def admission29_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1031120809376096826368/1416659293717101:ℝ), (75362280572732320768/52468862730263:ℝ), (1003732766087675834368/1416659293717101:ℝ)],
![(1003630522963301141120/1416659293717101:ℝ), (73327647046243907456/52468862730263:ℝ), (976289747285284360192/1416659293717101:ℝ)]]
theorem admission29_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (238351989083321377/483553038922103808:ℝ) admission29_03_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission29_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_03_coefficients]
def admission29_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6238806611699887760/52468862730263:ℝ), (12206406615507389440/52468862730263:ℝ), (5968883019164221440/52468862730263:ℝ)],
![(6543998852471490490/52468862730263:ℝ), (1830001561693326464/7495551818609:ℝ), (895332452874633216/7495551818609:ℝ)]]
theorem admission29_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (273233780784495/3358007214736832:ℝ) admission29_04_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission29_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_04_coefficients]
def admission29_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(309448232724436384879/4684719886630625:ℝ), (39086375988970238298754/295137352857729375:ℝ), (19587668865949197401377/295137352857729375:ℝ)],
![(259481258268778595681/4684719886630625:ℝ), (32831042794258892891242/295137352857729375:ℝ), (16480168350409753997089/295137352857729375:ℝ)]]
theorem admission29_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (778443774806335787043/19649139359374376960000:ℝ) admission29_05_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission29_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_05_coefficients]
def admission29_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(26460099117156279621337693698690027520/1178669389136131925580579908499:ℝ), (25835827886687086600328371163287531520/392889796378710641860193302833:ℝ), (75653245137482022992976016578923069440/1178669389136131925580579908499:ℝ), (24605809128028343339712596787750502400/1178669389136131925580579908499:ℝ)],
![(27627881594526709734186520211839957504/1178669389136131925580579908499:ℝ), (26993684164594144920539342360417271296/392889796378710641860193302833:ℝ), (553681441795801583499768511562144923648/8250685723952923479064059359493:ℝ), (180208876228524589584553163476261928960/8250685723952923479064059359493:ℝ)]]
theorem admission29_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (5866482049948774180343770214975/50289893936474962158104742762624:ℝ) admission29_06_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission29_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_06_coefficients]
def admission29_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2902577284484335313996641192159280/8258944668621545024088147507:ℝ), (51435886788434332166002434411320320/74330502017593905216793327563:ℝ), (937625967965333537874346973552640/2752981556207181674696049169:ℝ)],
![(2724497542460779930304947413781982/8258944668621545024088147507:ℝ), (48256503356976597157314210555628672/74330502017593905216793327563:ℝ), (879227118749499615100166193192960/2752981556207181674696049169:ℝ)]]
theorem admission29_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (321982587432678081701721018015/1409526556778077017444377174528:ℝ) admission29_07_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission29_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_07_coefficients]
def admission29_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(42811919277799164399397991092013017087272084418529/65839801248577367857845563671875000000000000:ℝ), (8420672960955865500701910935689519789384025425207457/4147907478660374175044270511328125000000000000:ℝ), (183746426422748282548753306568624904838107240212618143/87106057051867857675929680737890625000000000000:ℝ), (63551767255164273301057424910309450938406798968975413/87106057051867857675929680737890625000000000000:ℝ)],
![(1603356561887696139460759823893533797727327637122277/1316796024971547357156911273437500000000000000:ℝ), (307892108688530590997963450831650351837951531288768003/82958149573207483500885410226562500000000000000:ℝ), (1642002656647330848884447650404976182472966106046214523/435530285259339288379648403689453125000000000000:ℝ), (889401121428320339321311139833293190856660317413401/696848456414942861407437445903125000000000000:ℝ)]]
theorem admission29_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (42811919277799164399397991092013017087272084418529/11782491380740823394800344707891200000000000000000000:ℝ) admission29_08_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission29_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_08_coefficients]
def admission29_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3941065095308376909912162623640156720716/2280263273609106221882975935546875:ℝ), (48523519916767863593144022786475908695156/9678450783540873075103297859765625:ℝ), (2109179172179462955347318176784862904079872/435530285259339288379648403689453125:ℝ), (678367103375424461471064153677949915204608/435530285259339288379648403689453125:ℝ)],
![(4818621500162523007452990940832619526867621/4355302852593392883796484036894531250:ℝ), (1533603308817419460133528147682816468230057/483922539177043653755164892988281250:ℝ), (6575603277800271335312413174903036465211456/2177651426296696441898242018447265625:ℝ), (416742794243409816160160435847798217290752/435530285259339288379648403689453125:ℝ)]]
theorem admission29_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (406975385003329898593906675632615446573/76114434066016158941996367424512000000000:ℝ) admission29_09_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission29_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_09_coefficients]
def admission29_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(561884583191094771421446299648/13834563415206064453125:ℝ), (539399927243750458696157339648/4611521138402021484375:ℝ), (1550933589272005503312605138944/13834563415206064453125:ℝ), (164873434410616299548526473216/4611521138402021484375:ℝ)],
![(896677295930474729163578561536/13834563415206064453125:ℝ), (853863027680358547689236816896/4611521138402021484375:ℝ), (811157893274144992012095072256/4611521138402021484375:ℝ), (768565813336834062132153327616/13834563415206064453125:ℝ)],
![(65719353618647663217668916544/2766912683041212890625:ℝ), (308335084791547848634151008064/4611521138402021484375:ℝ), (864358509528032057280387300224/13834563415206064453125:ℝ), (267952032566939327466278858752/13834563415206064453125:ℝ)]]
theorem admission29_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (65417976700912921744696987/51578990818357739520000000000:ℝ) admission29_10_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission29_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_10_coefficients]
def admission29_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7140733652879862585745385533704560/24776834005864635072264442521:ℝ), (14060557811226431146179758497331200/24776834005864635072264442521:ℝ), (20762539815169975547069921048145920/74330502017593905216793327563:ℝ)],
![(6691482816165486835881833510962406/24776834005864635072264442521:ℝ), (13169509822819007357933409724073728/24776834005864635072264442521:ℝ), (19437041620337591539561432016015360/74330502017593905216793327563:ℝ)]]
theorem admission29_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (4745371489340232309463240238285/25371478022005386313998789141504:ℝ) admission29_11_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission29_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_11_coefficients]
def admission29_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission29_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission29_12_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission29_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_12_coefficients]
def admission29_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission29_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission29_13_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission29_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_13_coefficients]
def admission29_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission29_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission29_14_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission29_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_14_coefficients]
theorem admission29_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission29_00_pos hδ hp
 · exact admission29_01_pos hδ hp
 · exact admission29_02_pos hδ hp
 · exact admission29_03_pos hδ hp
 · exact admission29_04_pos hδ hp
 · exact admission29_05_pos hδ hp
 · exact admission29_06_pos hδ hp
 · exact admission29_07_pos hδ hp
 · exact admission29_08_pos hδ hp
 · exact admission29_09_pos hδ hp
 · exact admission29_10_pos hδ hp
 · exact admission29_11_pos hδ hp
 · exact admission29_12_pos hδ hp
 · exact admission29_13_pos hδ hp
 · exact admission29_14_pos hδ hp
#print axioms admission29_all
end
end Record1252270103Finite
