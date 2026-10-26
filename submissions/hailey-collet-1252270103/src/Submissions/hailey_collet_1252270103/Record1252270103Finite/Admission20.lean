/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission20_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19142460698717029/157406588190789:ℝ), (18785054110526240/157406588190789:ℝ)]]
theorem admission20_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission20_00_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission20_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_00_coefficients]
def admission20_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(13948043288420992/157406588190789:ℝ), (13748043288420992/157406588190789:ℝ)]]
theorem admission20_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission20_01_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission20_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_01_coefficients]
def admission20_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2363670313279018/52468862730263:ℝ), (2331594929361024/52468862730263:ℝ)]]
theorem admission20_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission20_02_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission20_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_02_coefficients]
def admission20_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2076057663374197811968/1416659293717101:ℝ), (151744603887064637696/52468862730263:ℝ), (2021187041576547405824/1416659293717101:ℝ)],
![(2048567376961402126720/1416659293717101:ℝ), (149709970360576224384/52468862730263:ℝ), (1993744022774155931648/1416659293717101:ℝ)]]
theorem admission20_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (486753911810096663/967106077844207616:ℝ) admission20_03_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission20_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_03_coefficients]
def admission20_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(12165672892814781132/52468862730263:ℝ), (23802492900239409408/52468862730263:ℝ), (11639321887370231808/52468862730263:ℝ)],
![(12470865133586383862/52468862730263:ℝ), (24406097216585305216/52468862730263:ℝ), (11937766038328442880/52468862730263:ℝ)]]
theorem admission20_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2131223490119061/26864057717894656:ℝ) admission20_04_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission20_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_04_coefficients]
def admission20_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(643879952676701664357/4684719886630625:ℝ), (16247932039048769050822/59027470571545875:ℝ), (40668459676917620532119/295137352857729375:ℝ)],
![(593912978221043875159/4684719886630625:ℝ), (74984327000532499846598/295137352857729375:ℝ), (37560959161378177127831/295137352857729375:ℝ)]]
theorem admission20_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1781738934663131625477/39298278718748753920000:ℝ) admission20_05_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission20_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_05_coefficients]
def admission20_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(362060645289328079325409126559569777664/8250685723952923479064059359493:ℝ), (353459814855246582128208585488217496576/2750228574650974493021353119831:ℝ), (1034832617254872035423486398971581333504/8250685723952923479064059359493:ℝ), (336513115460070620549411369066498621440/8250685723952923479064059359493:ℝ)],
![(370235122630921090115350912151619287552/8250685723952923479064059359493:ℝ), (361564808800595990369685383868125675008/2750228574650974493021353119831:ℝ), (1058941343088299457972422794481264771072/8250685723952923479064059359493:ℝ), (49211618256056686679425193575501004800/1178669389136131925580579908499:ℝ)]]
theorem admission20_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (320923915348120327519809121195315/2816234060442597880853865594706944:ℝ) admission20_06_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission20_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_06_coefficients]
def admission20_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5898519231544528742892856429454596/8258944668621545024088147507:ℝ), (104500233653301586604672673324889856/74330502017593905216793327563:ℝ), (1904451360538584037135784337285120/2752981556207181674696049169:ℝ)],
![(5720439489520973359201162651077298/8258944668621545024088147507:ℝ), (101320850221843851595984449469198208/74330502017593905216793327563:ℝ), (1846052511322750114361603556925440/2752981556207181674696049169:ℝ)]]
theorem admission20_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (676044620845733684458595052585/2819053113556154034888754349056:ℝ) admission20_07_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission20_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_07_coefficients]
def admission20_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(965358594780253724503119641627247227508997427989463/1316796024971547357156911273437500000000000000:ℝ), (199074954826101786988585173579929562655395415753131287/82958149573207483500885410226562500000000000000:ℝ), (4529004902501784120320226530399625274056955699235220649/1742121141037357153518593614757812500000000000000:ℝ), (1625573120558396269976552696374770903053277440649523171/1742121141037357153518593614757812500000000000000:ℝ)],
![(42811919277799164399397991092013017087272084418529/32919900624288683928922781835937500000000000:ℝ), (6771072085910301359450208113955790374113328770755003/1659162991464149670017708204531250000000000000:ℝ), (7422087000636141864882951000647031907186675319167715881/1742121141037357153518593614757812500000000000000:ℝ), (2578040579025911652258682047751814861426792254803517411/1742121141037357153518593614757812500000000000000:ℝ)]]
theorem admission20_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (965358594780253724503119641627247227508997427989463/471299655229632935792013788315648000000000000000000000:ℝ) admission20_08_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission20_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_08_coefficients]
def admission20_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(8274064845425366948579692397746641411913579/2177651426296696441898242018447265625:ℝ), (2664687910029330285903614836389395156500903/241961269588521826877582446494140625:ℝ), (3306547133216912416689457647816110278301824/311093060899528063128320288349609375:ℝ), (1487546361316856245597580166270975679366144/435530285259339288379648403689453125:ℝ)],
![(13839316858974257006680145125173203014127219/4355302852593392883796484036894531250:ℝ), (4436803133037686852283556681137811346474063/483922539177043653755164892988281250:ℝ), (2739362478488763353628860832241641984703552/311093060899528063128320288349609375:ℝ), (1225922052184841600286676448440823981452288/435530285259339288379648403689453125:ℝ)]]
theorem admission20_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1197189504086759375279957469180492169387/152228868132032317883992734849024000000000:ℝ) admission20_09_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission20_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_09_coefficients]
def admission20_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2460107440299011814280431524096/13834563415206064453125:ℝ), (2361820357935670392653767822592/4611521138402021484375:ℝ), (107802194298758041195405910528/219596244685810546875:ℝ), (309455982799286747375671488512/1976366202172294921875:ℝ)],
![(4490814918279160567817385689344/13834563415206064453125:ℝ), (859655824967459401467418759424/922304227680404296875:ℝ), (12319015808289950791216465714688/13834563415206064453125:ℝ), (1305002694362823445674190004224/4611521138402021484375:ℝ)],
![(404902306666801422376633297216/2766912683041212890625:ℝ), (1930330751256566374324397505344/4611521138402021484375:ℝ), (5509295986445796780462600573824/13834563415206064453125:ℝ), (1742822725955417269372574543872/13834563415206064453125:ℝ)]]
theorem admission20_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (425493829578959294280413707/206315963273430958080000000000:ℝ) admission20_10_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission20_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_10_coefficients]
def admission20_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(14517219881772284667463630596828148/24776834005864635072264442521:ℝ), (28577713404435325861343725509046784/24776834005864635072264442521:ℝ), (42187828727756143097894086612357120/74330502017593905216793327563:ℝ)],
![(14067969045057908917600078574085994/24776834005864635072264442521:ℝ), (27686665416027902073097376735789312/24776834005864635072264442521:ℝ), (40862330532923759090385597580226560/74330502017593905216793327563:ℝ)]]
theorem admission20_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (9976154915264589621676171284235/50742956044010772627997578283008:ℝ) admission20_11_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission20_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_11_coefficients]
def admission20_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission20_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission20_12_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission20_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_12_coefficients]
def admission20_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission20_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission20_13_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission20_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_13_coefficients]
def admission20_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission20_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission20_14_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission20_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_14_coefficients]
theorem admission20_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission20_00_pos hδ hp
 · exact admission20_01_pos hδ hp
 · exact admission20_02_pos hδ hp
 · exact admission20_03_pos hδ hp
 · exact admission20_04_pos hδ hp
 · exact admission20_05_pos hδ hp
 · exact admission20_06_pos hδ hp
 · exact admission20_07_pos hδ hp
 · exact admission20_08_pos hδ hp
 · exact admission20_09_pos hδ hp
 · exact admission20_10_pos hδ hp
 · exact admission20_11_pos hδ hp
 · exact admission20_12_pos hδ hp
 · exact admission20_13_pos hδ hp
 · exact admission20_14_pos hδ hp
#print axioms admission20_all
end
end Record1252270103Finite
