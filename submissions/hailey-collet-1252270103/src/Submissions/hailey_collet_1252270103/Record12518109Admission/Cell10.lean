/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell10 : Cell := ⟨(9763743/10000000:ℝ), (906637/250000:ℝ), (6239/10000:ℝ), (1/25:ℝ), (81/2000:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (139/25000:ℝ), (1/50:ℝ)⟩
def cell10_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(83666748646772754318528171075580783687634126837/765629029606135358383891753968750000000:ℝ), (4274683048630080525612297359693405209956258516989/574221772204601518787918815476562500000:ℝ), (1168449095250124406061537489856775320075074659927/54687787829009668455992268140625000000:ℝ), (3932503185975707533559553384939909397984240873163/191407257401533839595972938492187500000:ℝ), (15014347240912826411514296833335128039562097619489/2296887088818406075151675261906250000000:ℝ)],
  ![(31893042661740109941328717164414371628599042279/255209676535378452794630584656250000000:ℝ), (475601454245503382967544889187163962306389835221/63802419133844613198657646164062500000:ℝ), (2719106186338403732774103446500336009341840873163/127604838267689226397315292328125000000:ℝ), (1305701978462584898031122104754378653494746957721/63802419133844613198657646164062500000:ℝ), (1660802365339148184832804826355812837729121957721/255209676535378452794630584656250000000:ℝ)]]
theorem cell10_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highRegular cell10 2 b ν := by
 have heq : highRegular cell10 2 b ν = Record12518109.Bernstein.bsum 1 4 (83666748646772754318528171075580783687634126837/6056030324792529375000000000000000000000000000:ℝ) cell10_regular2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_regular2_g]
def cell10_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(2716533332017472591662681917430205807870905511/2296887088818406075151675261906250000000:ℝ), (1324910401568467088444682635880447647445825830663/191407257401533839595972938492187500000:ℝ), (7879061092898765614173734561848007174530554094489/382814514803067679191945876984375000000:ℝ), (11552495962942608776820850578862767292332754094489/574221772204601518787918815476562500000:ℝ), (1652523964711722115792365867471561062201903232721/255209676535378452794630584656250000000:ℝ)],
  ![(15870410275571284212549677392133367452359905511/2296887088818406075151675261906250000000:ℝ), (3961843414711495853102274614022168330638727491989/574221772204601518787918815476562500000:ℝ), (7842706629206750948416949980652837962030554094489/382814514803067679191945876984375000000:ℝ), (11495514067847498880043794726598071979832754094489/574221772204601518787918815476562500000:ℝ), (14798100366040245472437846832986237059817129094489/2296887088818406075151675261906250000000:ℝ)]]
theorem cell10_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highRegular cell10 3 b ν := by
 have heq : highRegular cell10 3 b ν = Record12518109.Bernstein.bsum 1 4 (2716533332017472591662681917430205807870905511/18168090974377588125000000000000000000000000000:ℝ) cell10_regular3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_regular3_g]
def cell10_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(239880038570685506286221113667676912852601515073/328126726974058010735953608843750000000:ℝ), (635682462632435965803290955316719418673699827427/82031681743514502683988402210937500000:ℝ), (7353952531704264939615423480409756919075725394489/382814514803067679191945876984375000000:ℝ), (10312453995985118993973867046741284320627925394489/574221772204601518787918815476562500000:ℝ), (13260298239843415080277440967743774400612300394489/2296887088818406075151675261906250000000:ℝ)],
  ![(182304706112885702529191073917939485001411067279/255209676535378452794630584656250000000:ℝ), (1465054040462347445530798423548646939672382930663/191407257401533839595972938492187500000:ℝ), (2428446681268378744835665526235279235525241798163/127604838267689226397315292328125000000:ℝ), (1136871166934529682391344146955732112014213932721/63802419133844613198657646164062500000:ℝ), (4389830723654564894589579060328653966870766798163/765629029606135358383891753968750000000:ℝ)]]
theorem cell10_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highRegular cell10 4 b ν := by
 have heq : highRegular cell10 4 b ν = Record12518109.Bernstein.bsum 1 4 (182304706112885702529191073917939485001411067279/2018676774930843125000000000000000000000000000:ℝ) cell10_regular4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_regular4_g]
def cell10_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(247191021695613939002892217720469331323/5227617112162828869822375000000000:ℝ), (387973320732376617984637180735900240643/2888946298826826480691312500000000:ℝ), (9707704061475746631872345699646889542217/109779959355419406266269875000000000:ℝ)],
  ![(1717512000812398992203212129886524319261/36593319785139802088756625000000000:ℝ), (2442685578965213714671947115072368190739/18296659892569901044378312500000000:ℝ), (459952221186556847840548599685566168677/5227617112162828869822375000000000:ℝ)]]
theorem cell10_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 0 false b ν := by
 have heq : highBranch cell10 0 false b ν = Record12518109.Bernstein.bsum 1 2 (1717512000812398992203212129886524319261/4602583046842322325000000000000000000000:ℝ) cell10_exceptional0_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional0_0_g]
def cell10_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(9253678687344962430808115982536517394505009/195946772215199314527552082125000000000:ℝ), (14530251623900846689592915073464552032521569/108286374118925936975752466437500000000:ℝ), (363659511722390451615695153021491412166894811/4114882216519185605078593724625000000000:ℝ)],
  ![(21431991169448682123309506895904274732845021/457209135168798400564288191625000000000:ℝ), (91483134608171274290286779706773118705969937/685813702753197600846432287437500000000:ℝ), (120612154668891414594551833695953387388964937/1371627405506395201692864574875000000000:ℝ)]]
theorem cell10_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 0 true b ν := by
 have heq : highBranch cell10 0 true b ν = Record12518109.Bernstein.bsum 1 2 (21431991169448682123309506895904274732845021/57506206781596922569325000000000000000000000:ℝ) cell10_exceptional0_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional0_1_g]
theorem cell10_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
 (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell10 0 b ν :=
 highExceptional_pos_of_branches (cell10_exceptional0_0 hb hν) (cell10_exceptional0_1 hb hν)
def cell10_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(4124496662602354554334594690654697051/825413228236236137340375000000000:ℝ), (8699639969478526170752112594766273661/45856290457568674296687500000000:ℝ), (1075479440003095071819522413780311620643/5777892597653652961382625000000000:ℝ)],
  ![(3108740878376819520814637274191764373/641988066405961440153625000000000:ℝ), (181994727500795510912037484095091746881/962982099608942160230437500000000:ℝ), (51055697790606166915143971191919600983/275137742745412045780125000000000:ℝ)]]
theorem cell10_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 1 false b ν := by
 have heq : highBranch cell10 1 false b ν = Record12518109.Bernstein.bsum 1 2 (3108740878376819520814637274191764373/80747070997233725000000000000000000000:ℝ) cell10_exceptional1_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional1_0_g]
def cell10_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(152738132792997501312129978956151922487633/30938964033978839135929276125000000000:ℝ), (6843809918791626831515916706829043385840523/36095458039641978991917488812500000000:ℝ), (5757273394956235184785233332634947673012367/30938964033978839135929276125000000000:ℝ)],
  ![(345283812606010501726375695433812508804477/72190916079283957983834977625000000000:ℝ), (6817705794692221747265279226468720885840523/36095458039641978991917488812500000000:ℝ), (13392330879983428381430856176983627903695523/72190916079283957983834977625000000000:ℝ)]]
theorem cell10_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 1 true b ν := by
 have heq : highBranch cell10 1 true b ν = Record12518109.Bernstein.bsum 1 2 (345283812606010501726375695433812508804477/9079927386567935142525000000000000000000000:ℝ) cell10_exceptional1_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional1_1_g]
theorem cell10_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
 (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell10 1 b ν :=
 highExceptional_pos_of_branches (cell10_exceptional1_0 hb hν) (cell10_exceptional1_1 hb hν)
def cell10_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(244256320317359434553372555456454216857/2888946298826826480691312500000000:ℝ), (2693897556863117088094031384573551/24074552490223554005760937500:ℝ), (4051101889901801463973696298549/132066116517797781974460000:ℝ)],
  ![(81034907579521295875987677886841905619/962982099608942160230437500000000:ℝ), (2677947192623804526861683593448551/24074552490223554005760937500:ℝ), (1338429773818448928641715766183/44022038839265927324820000:ℝ)]]
theorem cell10_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 2 false b ν := by
 have heq : highBranch cell10 2 false b ν = Record12518109.Bernstein.bsum 1 2 (1338429773818448928641715766183/5536942011238884000000000000000:ℝ) cell10_exceptional2_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional2_0_g]
def cell10_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(9148515718506208612317454285440208894675931/108286374118925936975752466437500000000:ℝ), (806935057009182386018728403324315356429/7219091607928395798383497762500000:ℝ), (151569798937775954594770897400447957/4950234245436614261748684180000:ℝ)],
  ![(3035141738486660450875247573754519476391977/36095458039641978991917488812500000000:ℝ), (802161758883627625328909998783500856429/7219091607928395798383497762500000:ℝ), (16692291918525858391706787527049773/550026027270734917972076020000:ℝ)]]
theorem cell10_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 2 true b ν := by
 have heq : highBranch cell10 2 true b ν = Record12518109.Bernstein.bsum 1 2 (16692291918525858391706787527049773/69180399135755696324000000000000000:ℝ) cell10_exceptional2_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional2_1_g]
theorem cell10_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
 (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell10 2 b ν :=
 highExceptional_pos_of_branches (cell10_exceptional2_0 hb hν) (cell10_exceptional2_1 hb hν)
def cell10_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(227768521393892020611213665220469331323/5227617112162828869822375000000000:ℝ), (6881030049791649672723406036482104572217/54889979677709703133134937500000000:ℝ), (9139041677939111556378845302146889542217/109779959355419406266269875000000000:ℝ)],
  ![(83239710457912924392708540125606543119/1925964199217884320460875000000000:ℝ), (119957784083721667983002472766966746881/962982099608942160230437500000000:ℝ), (7594264211680082480499599161150283661/91712580915137348593375000000000:ℝ)]]
theorem cell10_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 3 false b ν := by
 have heq : highBranch cell10 3 false b ν = Record12518109.Bernstein.bsum 1 2 (83239710457912924392708540125606543119/242241212991701175000000000000000000000:ℝ) cell10_exceptional3_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional3_0_g]
def cell10_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(8525665108535519763732828799179017394505009/195946772215199314527552082125000000000:ℝ), (257690754571234709118511861396333988617909811/2057441108259592802539296862312500000000:ℝ), (342344339600286759080972277621998912166894811/4114882216519185605078593724625000000000:ℝ)],
  ![(3115783076667365668442184758116332852554477/72190916079283957983834977625000000000:ℝ), (4492375044590042892756259896856611510840523/36095458039641978991917488812500000000:ℝ), (1991352584120295621338787284727296269981841/24063638693094652661278325875000000000:ℝ)]]
theorem cell10_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 3 true b ν := by
 have heq : highBranch cell10 3 true b ν = Record12518109.Bernstein.bsum 1 2 (3115783076667365668442184758116332852554477/9079927386567935142525000000000000000000000:ℝ) cell10_exceptional3_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional3_1_g]
theorem cell10_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
 (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell10 3 b ν :=
 highExceptional_pos_of_branches (cell10_exceptional3_0 hb hν) (cell10_exceptional3_1 hb hν)
def cell10_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(1788366918063570026237652190654697051/825413228236236137340375000000000:ℝ), (8236393883590316423780245094766273661/45856290457568674296687500000000:ℝ), (1033694457096858281516201011280311620643/5777892597653652961382625000000000:ℝ)],
  ![(1291751077068875998961459774191764373/641988066405961440153625000000000:ℝ), (172266559697143106225628266595091746881/962982099608942160230437500000000:ℝ), (49065936699832986424509618691919600983/275137742745412045780125000000000:ℝ)]]
theorem cell10_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 4 false b ν := by
 have heq : highBranch cell10 4 false b ν = Record12518109.Bernstein.bsum 1 2 (1291751077068875998961459774191764373/80747070997233725000000000000000000000:ℝ) cell10_exceptional4_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional4_0_g]
def cell10_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(65172981578450240845472283228651922487633/30938964033978839135929276125000000000:ℝ), (6479169005007323746655240007276543385840523/36095458039641978991917488812500000000:ℝ), (5533526750059881811793891028362447673012367/30938964033978839135929276125000000000:ℝ)],
  ![(140965126438733560637507738736312508804477/72190916079283957983834977625000000000:ℝ), (6453064880907918662404602526916220885840523/36095458039641978991917488812500000000:ℝ), (12870255375225270511117724133681127903695523/72190916079283957983834977625000000000:ℝ)]]
theorem cell10_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 4 true b ν := by
 have heq : highBranch cell10 4 true b ν = Record12518109.Bernstein.bsum 1 2 (140965126438733560637507738736312508804477/9079927386567935142525000000000000000000000:ℝ) cell10_exceptional4_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional4_1_g]
theorem cell10_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
 (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell10 4 b ν :=
 highExceptional_pos_of_branches (cell10_exceptional4_0 hb hν) (cell10_exceptional4_1 hb hν)
def cell10_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(35507660325913424644154897230279697051/825413228236236137340375000000000:ℝ), (758526261351858157915978702065409896998689/7742788787470013086321387687500000000:ℝ), (902386716951883403675309611286110214626189/15485577574940026172642775375000000000:ℝ)],
  ![(27404761753800833064225900360566764373/641988066405961440153625000000000:ℝ), (1757478632865560999121416411311565592996941/18066507170763363868083237937500000000:ℝ), (2092424272839628551794968740723840500794441/36133014341526727736166475875000000000:ℝ)]]
theorem cell10_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 5 false b ν := by
 have heq : highBranch cell10 5 false b ν = Record12518109.Bernstein.bsum 1 2 (27404761753800833064225900360566764373/80747070997233725000000000000000000000:ℝ) cell10_exceptional5_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional5_0_g]
def cell10_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(1329073256384886341488864379048915797487633/30938964033978839135929276125000000000:ℝ), (198794888608005687201648573206421725130225518509/2031560664845169503602092022833937500000000:ℝ), (236557465984948385494715401828928521716757621009/4063121329690339007204184045667875000000000:ℝ)],
  ![(3077347064026565400669428818233594883804477/72190916079283957983834977625000000000:ℝ), (21933493087744864863366045315161770688913946501/225728962760574389289121335870437500000000:ℝ), (78360657625310491691915301527075863488919207003/1354373776563446335734728015222625000000000:ℝ)]]
theorem cell10_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 5 true b ν := by
 have heq : highBranch cell10 5 true b ν = Record12518109.Bernstein.bsum 1 2 (3077347064026565400669428818233594883804477/9079927386567935142525000000000000000000000:ℝ) cell10_exceptional5_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional5_1_g]
theorem cell10_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
 (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell10 5 b ν :=
 highExceptional_pos_of_branches (cell10_exceptional5_0 hb hν) (cell10_exceptional5_1 hb hν)
def cell10_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(244256320317359434553372555456454216857/2888946298826826480691312500000000:ℝ), (2693897556863117088094031384573551/24074552490223554005760937500:ℝ), (4051101889901801463973696298549/132066116517797781974460000:ℝ)],
  ![(81034907579521295875987677886841905619/962982099608942160230437500000000:ℝ), (2677947192623804526861683593448551/24074552490223554005760937500:ℝ), (1338429773818448928641715766183/44022038839265927324820000:ℝ)]]
theorem cell10_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 6 false b ν := by
 have heq : highBranch cell10 6 false b ν = Record12518109.Bernstein.bsum 1 2 (1338429773818448928641715766183/5536942011238884000000000000000:ℝ) cell10_exceptional6_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional6_0_g]
def cell10_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(9148515718506208612317454285440208894675931/108286374118925936975752466437500000000:ℝ), (806935057009182386018728403324315356429/7219091607928395798383497762500000:ℝ), (151569798937775954594770897400447957/4950234245436614261748684180000:ℝ)],
  ![(3035141738486660450875247573754519476391977/36095458039641978991917488812500000000:ℝ), (802161758883627625328909998783500856429/7219091607928395798383497762500000:ℝ), (16692291918525858391706787527049773/550026027270734917972076020000:ℝ)]]
theorem cell10_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 6 true b ν := by
 have heq : highBranch cell10 6 true b ν = Record12518109.Bernstein.bsum 1 2 (16692291918525858391706787527049773/69180399135755696324000000000000000:ℝ) cell10_exceptional6_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional6_1_g]
theorem cell10_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
 (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell10 6 b ν :=
 highExceptional_pos_of_branches (cell10_exceptional6_0 hb hν) (cell10_exceptional6_1 hb hν)
def cell10_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(32514676229403857258532954730279697051/825413228236236137340375000000000:ℝ), (695239533606421615036344708315409896998689/7742788787470013086321387687500000000:ℝ), (831964636095626311637694887028610214626189/15485577574940026172642775375000000000:ℝ)],
  ![(25076885234293391764297722860566764373/641988066405961440153625000000000:ℝ), (536603200486514133022979030853855197665647/6022169056921121289361079312500000000:ℝ), (642702028058342890124622572485446833598147/12044338113842242578722158625000000000:ℝ)]]
theorem cell10_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 7 false b ν := by
 have heq : highBranch cell10 7 false b ν = Record12518109.Bernstein.bsum 1 2 (25076885234293391764297722860566764373/80747070997233725000000000000000000000:ℝ) cell10_exceptional7_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional7_0_g]
def cell10_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(1216887233495418227173597108321415797487633/30938964033978839135929276125000000000:ℝ), (182189653695430301644347326292302975130225518509/2031560664845169503602092022833937500000000:ℝ), (218080049987802793428794012863521414216757621009/4063121329690339007204184045667875000000000:ℝ)],
  ![(2815579677284473133933805186536094883804477/72190916079283957983834977625000000000:ℝ), (60265400959042799404331053640779062066741839503/677186888281723167867364007611312500000000:ℝ), (24067172986531764778869390623980053662973069001/451457925521148778578242671740875000000000:ℝ)]]
theorem cell10_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell10 7 true b ν := by
 have heq : highBranch cell10 7 true b ν = Record12518109.Bernstein.bsum 1 2 (2815579677284473133933805186536094883804477/9079927386567935142525000000000000000000000:ℝ) cell10_exceptional7_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_exceptional7_1_g]
theorem cell10_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
 (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell10 7 b ν :=
 highExceptional_pos_of_branches (cell10_exceptional7_0 hb hν) (cell10_exceptional7_1 hb hν)
def cell10_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(404080526255962032565828693579/36319709546271740570100000000000:ℝ)],
  ![(723163729779124820961079693579/36319709546271740570100000000000:ℝ)]]
theorem cell10_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 0 false b := by
 have heq : domainBranch cell10 0 false b = Record12518109.Bernstein.bsum 1 0 (404080526255962032565828693579/72639419092543481140200000000000000:ℝ) cell10_domain0_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain0_0_g]
def cell10_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(404080526255962032565828693579/36319709546271740570100000000000:ℝ)],
  ![(723163729779124820961079693579/36319709546271740570100000000000:ℝ)]]
theorem cell10_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 0 true b := by
 have heq : domainBranch cell10 0 true b = Record12518109.Bernstein.bsum 1 0 (404080526255962032565828693579/72639419092543481140200000000000000:ℝ) cell10_domain0_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain0_1_g]
def cell10_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(190975382010495292779006937047937/13842355028097210000000000000000:ℝ)],
  ![(435245583461861043829951291111853/32298828398893490000000000000000:ℝ)]]
theorem cell10_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 1 false b := by
 have heq : domainBranch cell10 1 false b = Record12518109.Bernstein.bsum 1 0 (435245583461861043829951291111853/64597656797786980000000000000000000:ℝ) cell10_domain1_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain1_0_g]
def cell10_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(345354124415029387900994164884259/13842355028097210000000000000000:ℝ)],
  ![(795462649072440599114588156063271/32298828398893490000000000000000:ℝ)]]
theorem cell10_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 1 true b := by
 have heq : domainBranch cell10 1 true b = Record12518109.Bernstein.bsum 1 0 (795462649072440599114588156063271/64597656797786980000000000000000000:ℝ) cell10_domain1_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain1_1_g]
def cell10_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(206306835831453180379365367846363/9689648519668047000000000000000:ℝ)],
  ![(207583142531392750396993265846363/9689648519668047000000000000000:ℝ)]]
theorem cell10_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 2 false b := by
 have heq : domainBranch cell10 2 false b = Record12518109.Bernstein.bsum 1 0 (206306835831453180379365367846363/19379297039336094000000000000000000:ℝ) cell10_domain2_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain2_0_g]
def cell10_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(103419886856800726188499385649841/9689648519668047000000000000000:ℝ)],
  ![(104696193556740296206127283649841/9689648519668047000000000000000:ℝ)]]
theorem cell10_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 2 true b := by
 have heq : domainBranch cell10 2 true b = Record12518109.Bernstein.bsum 1 0 (103419886856800726188499385649841/19379297039336094000000000000000000:ℝ) cell10_domain2_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain2_1_g]
def cell10_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(633335381323544647506433076957/32298828398893490000000000000:ℝ)],
  ![(789357994278588328628279076957/32298828398893490000000000000:ℝ)]]
theorem cell10_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 3 false b := by
 have heq : domainBranch cell10 3 false b = Record12518109.Bernstein.bsum 1 0 (633335381323544647506433076957/64597656797786980000000000000000:ℝ) cell10_domain3_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain3_0_g]
def cell10_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(633335381323544647506433076957/32298828398893490000000000000:ℝ)],
  ![(789357994278588328628279076957/32298828398893490000000000000:ℝ)]]
theorem cell10_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 3 true b := by
 have heq : domainBranch cell10 3 true b = Record12518109.Bernstein.bsum 1 0 (633335381323544647506433076957/64597656797786980000000000000000:ℝ) cell10_domain3_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain3_1_g]
def cell10_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(230700806893706657387291/14419119820934593750000:ℝ)],
  ![(1400384229076478978711037/100933838746542156250000:ℝ)]]
theorem cell10_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 4 false b := by
 have heq : domainBranch cell10 4 false b = Record12518109.Bernstein.bsum 1 0 (1400384229076478978711037/201867677493084312500000000:ℝ) cell10_domain4_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain4_0_g]
def cell10_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(230700806893706657387291/14419119820934593750000:ℝ)],
  ![(1400384229076478978711037/100933838746542156250000:ℝ)]]
theorem cell10_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 4 true b := by
 have heq : domainBranch cell10 4 true b = Record12518109.Bernstein.bsum 1 0 (1400384229076478978711037/201867677493084312500000000:ℝ) cell10_domain4_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain4_1_g]
def cell10_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(8432537695322373263004401909543/692117751404860500000000000000:ℝ)],
  ![(19169878715854326787101353122267/1614941419944674500000000000000:ℝ)]]
theorem cell10_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 5 false b := by
 have heq : domainBranch cell10 5 false b = Record12518109.Bernstein.bsum 1 0 (19169878715854326787101353122267/3229882839889349000000000000000000:ℝ) cell10_domain5_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain5_0_g]
def cell10_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(16136775799076345493025273770101/692117751404860500000000000000:ℝ)],
  ![(37146434291280261990483387463569/1614941419944674500000000000000:ℝ)]]
theorem cell10_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 5 true b := by
 have heq : domainBranch cell10 5 true b = Record12518109.Bernstein.bsum 1 0 (37146434291280261990483387463569/3229882839889349000000000000000000:ℝ) cell10_domain5_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain5_1_g]
def cell10_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(68709829140621086647696861992800677/469299900282668195118500000000000:ℝ)],
  ![(472827707027148791200492211983604739/3285099301978677365829500000000000:ℝ)]]
theorem cell10_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 6 false b := by
 have heq : domainBranch cell10 6 false b = Record12518109.Bernstein.bsum 1 0 (472827707027148791200492211983604739/6570198603957354731659000000000000000:ℝ) cell10_domain6_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain6_0_g]
def cell10_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(66679479214977360874059025342853599/469299900282668195118500000000000:ℝ)],
  ![(458615257547642710785027355433975193/3285099301978677365829500000000000:ℝ)]]
theorem cell10_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 6 true b := by
 have heq : domainBranch cell10 6 true b = Record12518109.Bernstein.bsum 1 0 (458615257547642710785027355433975193/6570198603957354731659000000000000000:ℝ) cell10_domain6_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain6_1_g]
def cell10_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(126753719227237859044495477939/2422412129917011750000000000:ℝ)],
  ![(139590709185166483237586477939/2422412129917011750000000000:ℝ)]]
theorem cell10_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 7 false b := by
 have heq : domainBranch cell10 7 false b = Record12518109.Bernstein.bsum 1 0 (126753719227237859044495477939/4844824259834023500000000000000:ℝ) cell10_domain7_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain7_0_g]
def cell10_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(126753719227237859044495477939/2422412129917011750000000000:ℝ)],
  ![(139590709185166483237586477939/2422412129917011750000000000:ℝ)]]
theorem cell10_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 7 true b := by
 have heq : domainBranch cell10 7 true b = Record12518109.Bernstein.bsum 1 0 (126753719227237859044495477939/4844824259834023500000000000000:ℝ) cell10_domain7_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain7_1_g]
def cell10_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(5221514481536987478998155137649/69211775140486050000000000000:ℝ)],
  ![(11938570780591980534776421321181/161494141994467450000000000000:ℝ)]]
theorem cell10_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 8 false b := by
 have heq : domainBranch cell10 8 false b = Record12518109.Bernstein.bsum 1 0 (11938570780591980534776421321181/322988283988934900000000000000000:ℝ) cell10_domain8_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain8_0_g]
def cell10_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(5518126269855564820660870403443/69211775140486050000000000000:ℝ)],
  ![(12630664953335327665322756941367/161494141994467450000000000000:ℝ)]]
theorem cell10_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell10 8 true b := by
 have heq : domainBranch cell10 8 true b = Record12518109.Bernstein.bsum 1 0 (12630664953335327665322756941367/322988283988934900000000000000000:ℝ) cell10_domain8_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_domain8_1_g]
def cell10_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(2260335368165490027933377/290689455590041410000000:ℝ)],
  ![(2474856787344957650933377/290689455590041410000000:ℝ)]]
theorem cell10_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell10 0 b := by
 have heq : ordinary cell10 0 b = Record12518109.Bernstein.bsum 1 0 (2260335368165490027933377/581378911180082820000000000:ℝ) cell10_ordinary0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordinary0_g]
def cell10_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(246112107041637511938089/41527065084291630000000:ℝ)],
  ![(167584814456888328951847/32298828398893490000000:ℝ)]]
theorem cell10_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell10 1 b := by
 have heq : ordinary cell10 1 b = Record12518109.Bernstein.bsum 1 0 (167584814456888328951847/64597656797786980000000000:ℝ) cell10_ordinary1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordinary1_g]
def cell10_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(13150227344592252233466457/13842355028097210000000:ℝ)],
  ![(30540849524595610129421733/32298828398893490000000:ℝ)]]
theorem cell10_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell10 2 b := by
 have heq : ordinary cell10 2 b = Record12518109.Bernstein.bsum 1 0 (30540849524595610129421733/64597656797786980000000000:ℝ) cell10_ordinary2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordinary2_g]
def cell10_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(399999989/10000000:ℝ)],
  ![(409999989/10000000:ℝ)]]
theorem cell10_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell10 3 b := by
 have heq : ordinary cell10 3 b = Record12518109.Bernstein.bsum 1 0 (399999989/20000000000:ℝ) cell10_ordinary3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordinary3_g]
def cell10_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(12133644821781974192880319/13842355028097210000000:ℝ)],
  ![(28104225981240507721387411/32298828398893490000000:ℝ)]]
theorem cell10_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell10 4 b := by
 have heq : ordinary cell10 4 b = Record12518109.Bernstein.bsum 1 0 (28104225981240507721387411/64597656797786980000000000:ℝ) cell10_ordinary4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordinary4_g]
def cell10_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(45224505331548668047/4574854875180000000000000:ℝ)],
  ![(45224505331548668047/4574854875180000000000000:ℝ)]]
theorem cell10_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell10 5 b := by
 have heq : ordinary cell10 5 b = Record12518109.Bernstein.bsum 1 0 (45224505331548668047/9149709750360000000000000000:ℝ) cell10_ordinary5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordinary5_g]
def cell10_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(2260306299219931023792377/290689455590041410000000:ℝ)],
  ![(2474827718399398646792377/290689455590041410000000:ℝ)]]
theorem cell10_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 0 false b := by
 have heq : complementBranch cell10 0 false b = Record12518109.Bernstein.bsum 1 0 (2260306299219931023792377/581378911180082820000000000:ℝ) cell10_complement0_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement0_0_g]
def cell10_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(117089261656720194158111171514797/15565589805545031672900000000000:ℝ)],
  ![(128621854050229195860609064514797/15565589805545031672900000000000:ℝ)]]
theorem cell10_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 0 true b := by
 have heq : complementBranch cell10 0 true b = Record12518109.Bernstein.bsum 1 0 (117089261656720194158111171514797/31131179611090063345800000000000000:ℝ) cell10_complement0_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement0_1_g]
def cell10_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(93789199567335588693594570169/1038176627107290750000000000:ℝ)],
  ![(216265654926314490037992997061/2422412129917011750000000000:ℝ)]]
theorem cell10_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 1 false b := by
 have heq : complementBranch cell10 1 false b = Record12518109.Bernstein.bsum 1 0 (216265654926314490037992997061/4844824259834023500000000000000:ℝ) cell10_complement1_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement1_0_g]
def cell10_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(7011168763235360479192927621713239/77827949027725158364500000000000:ℝ)],
  ![(16166827358976419051609648276330891/181598547731358702850500000000000:ℝ)]]
theorem cell10_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 1 true b := by
 have heq : complementBranch cell10 1 true b = Record12518109.Bernstein.bsum 1 0 (16166827358976419051609648276330891/363197095462717405701000000000000000:ℝ) cell10_complement1_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement1_1_g]
def cell10_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(7003443351012277765267052241/115352958567476750000000000:ℝ)],
  ![(45781928555935676241182365687/807470709972337250000000000:ℝ)]]
theorem cell10_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 2 false b := by
 have heq : complementBranch cell10 2 false b = Record12518109.Bernstein.bsum 1 0 (45781928555935676241182365687/1614941419944674500000000000000:ℝ) cell10_complement2_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement2_0_g]
def cell10_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(522816537415373163527556179901471/8647549891969462040500000000000:ℝ)],
  ![(10250520440143148706710896936930891/181598547731358702850500000000000:ℝ)]]
theorem cell10_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 2 true b := by
 have heq : complementBranch cell10 2 true b = Record12518109.Bernstein.bsum 1 0 (10250520440143148706710896936930891/363197095462717405701000000000000000:ℝ) cell10_complement2_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement2_1_g]
def cell10_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(80715219377246045895142345169/1038176627107290750000000000:ℝ)],
  ![(187547379642601120366604472061/2422412129917011750000000000:ℝ)]]
theorem cell10_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 3 false b := by
 have heq : complementBranch cell10 3 false b = Record12518109.Bernstein.bsum 1 0 (187547379642601120366604472061/4844824259834023500000000000000:ℝ) cell10_complement3_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement3_0_g]
def cell10_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(6031064764305107813764158122363239/77827949027725158364500000000000:ℝ)],
  ![(4671311044685854193608112037060297/60532849243786234283500000000000:ℝ)]]
theorem cell10_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 3 true b := by
 have heq : complementBranch cell10 3 true b = Record12518109.Bernstein.bsum 1 0 (4671311044685854193608112037060297/121065698487572468567000000000000000:ℝ) cell10_complement3_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement3_1_g]
def cell10_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(8541160355690878866040939741/115352958567476750000000000:ℝ)],
  ![(59227465328429229234099578187/807470709972337250000000000:ℝ)]]
theorem cell10_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 4 false b := by
 have heq : complementBranch cell10 4 false b = Record12518109.Bernstein.bsum 1 0 (59227465328429229234099578187/1614941419944674500000000000000:ℝ) cell10_complement4_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement4_0_g]
def cell10_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(638093030388109173648171430226471/8647549891969462040500000000000:ℝ)],
  ![(13274394769203403787711992193755891/181598547731358702850500000000000:ℝ)]]
theorem cell10_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 4 true b := by
 have heq : complementBranch cell10 4 true b = Record12518109.Bernstein.bsum 1 0 (13274394769203403787711992193755891/363197095462717405701000000000000000:ℝ) cell10_complement4_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement4_1_g]
def cell10_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(904131/12500:ℝ)],
  ![(1695813/25000:ℝ)]]
theorem cell10_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 5 false b := by
 have heq : complementBranch cell10 5 false b = Record12518109.Bernstein.bsum 1 0 (1695813/50000000:ℝ) cell10_complement5_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement5_0_g]
def cell10_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(124655567534697216661538156320533/1729509978393892408100000000000:ℝ)],
  ![(2454508678545734165940412703731193/36319709546271740570100000000000:ℝ)]]
theorem cell10_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 5 true b := by
 have heq : complementBranch cell10 5 true b = Record12518109.Bernstein.bsum 1 0 (2454508678545734165940412703731193/72639419092543481140200000000000000:ℝ) cell10_complement5_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement5_1_g]
def cell10_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(8228687459790642854403623/41527065084291630000000:ℝ)],
  ![(2671388680203725077134541/13842355028097210000000:ℝ)]]
theorem cell10_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 6 false b := by
 have heq : complementBranch cell10 6 false b = Record12518109.Bernstein.bsum 1 0 (2671388680203725077134541/27684710056194420000000000:ℝ) cell10_complement6_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement6_0_g]
def cell10_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(3080392446247422808553893423974797/15565589805545031672900000000000:ℝ)],
  ![(2333355862453133764306891024313731/12106569848757246856700000000000:ℝ)]]
theorem cell10_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 6 true b := by
 have heq : complementBranch cell10 6 true b = Record12518109.Bernstein.bsum 1 0 (2333355862453133764306891024313731/24213139697514493713400000000000000:ℝ) cell10_complement6_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement6_1_g]
def cell10_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(29103675441634830184540297061/14534472779502070500000000000:ℝ)],
  ![(32350850201421247012479297061/14534472779502070500000000000:ℝ)]]
theorem cell10_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 7 false b := by
 have heq : complementBranch cell10 7 false b = Record12518109.Bernstein.bsum 1 0 (29103675441634830184540297061/29068945559004141000000000000000:ℝ) cell10_complement7_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement7_0_g]
def cell10_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(476432086940485703550265801602679/272397821597038054275750000000000:ℝ)],
  ![(538086720709830741502072697602679/272397821597038054275750000000000:ℝ)]]
theorem cell10_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 7 true b := by
 have heq : complementBranch cell10 7 true b = Record12518109.Bernstein.bsum 1 0 (476432086940485703550265801602679/544795643194076108551500000000000000:ℝ) cell10_complement7_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement7_1_g]
def cell10_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(160390249691577611923738565687/4844824259834023500000000000:ℝ)],
  ![(175774069223470925733051565687/4844824259834023500000000000:ℝ)]]
theorem cell10_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 8 false b := by
 have heq : complementBranch cell10 8 false b = Record12518109.Bernstein.bsum 1 0 (160390249691577611923738565687/9689648519668047000000000000000:ℝ) cell10_complement8_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement8_0_g]
def cell10_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(426135578449294855964425848128699/12971324837954193060750000000000:ℝ)],
  ![(467361543653092166880745224128699/12971324837954193060750000000000:ℝ)]]
theorem cell10_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 8 true b := by
 have heq : complementBranch cell10 8 true b = Record12518109.Bernstein.bsum 1 0 (426135578449294855964425848128699/25942649675908386121500000000000000:ℝ) cell10_complement8_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement8_1_g]
def cell10_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(594187517483007337167884547061/14534472779502070500000000000:ℝ)],
  ![(651065047037660659745823547061/14534472779502070500000000000:ℝ)]]
theorem cell10_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 9 false b := by
 have heq : complementBranch cell10 9 false b = Record12518109.Bernstein.bsum 1 0 (594187517483007337167884547061/29068945559004141000000000000000:ℝ) cell10_complement9_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement9_0_g]
def cell10_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(11066950912558868543178612062977679/272397821597038054275750000000000:ℝ)],
  ![(12133718840716211695244043958977679/272397821597038054275750000000000:ℝ)]]
theorem cell10_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 9 true b := by
 have heq : complementBranch cell10 9 true b = Record12518109.Bernstein.bsum 1 0 (11066950912558868543178612062977679/544795643194076108551500000000000000:ℝ) cell10_complement9_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement9_1_g]
def cell10_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(2260306299219931023792377/290689455590041410000000:ℝ)],
  ![(2474827718399398646792377/290689455590041410000000:ℝ)]]
theorem cell10_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 10 false b := by
 have heq : complementBranch cell10 10 false b = Record12518109.Bernstein.bsum 1 0 (2260306299219931023792377/581378911180082820000000000:ℝ) cell10_complement10_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement10_0_g]
def cell10_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(117089261656720194158111171514797/15565589805545031672900000000000:ℝ)],
  ![(128621854050229195860609064514797/15565589805545031672900000000000:ℝ)]]
theorem cell10_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 10 true b := by
 have heq : complementBranch cell10 10 true b = Record12518109.Bernstein.bsum 1 0 (117089261656720194158111171514797/31131179611090063345800000000000000:ℝ) cell10_complement10_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement10_1_g]
def cell10_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(2260330523341230193909877/48448242598340235000000:ℝ)],
  ![(2474851942520697816909877/48448242598340235000000:ℝ)]]
theorem cell10_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 11 false b := by
 have heq : complementBranch cell10 11 false b = Record12518109.Bernstein.bsum 1 0 (2260330523341230193909877/96896485196680470000000000:ℝ) cell10_complement11_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement11_0_g]
def cell10_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(1685277453948131498319372235051193/36319709546271740570100000000000:ℝ)],
  ![(1846201942118052250840350652051193/36319709546271740570100000000000:ℝ)]]
theorem cell10_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 11 true b := by
 have heq : complementBranch cell10 11 true b = Record12518109.Bernstein.bsum 1 0 (1685277453948131498319372235051193/72639419092543481140200000000000000:ℝ) cell10_complement11_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement11_1_g]
def cell10_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(2260331215458981598770377/41527065084291630000000:ℝ)],
  ![(2474852634638449221770377/41527065084291630000000:ℝ)]]
theorem cell10_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 12 false b := by
 have heq : complementBranch cell10 12 false b = Record12518109.Bernstein.bsum 1 0 (2260331215458981598770377/83054130168583260000000000:ℝ) cell10_complement12_0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement12_0_g]
def cell10_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(5903073867893865122128384406063579/108959128638815221710300000000000:ℝ)],
  ![(6466256395954667228820409657063579/108959128638815221710300000000000:ℝ)]]
theorem cell10_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ))
    (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell10 12 true b := by
 have heq : complementBranch cell10 12 true b = Record12518109.Bernstein.bsum 1 0 (5903073867893865122128384406063579/217918257277630443420600000000000000:ℝ) cell10_complement12_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement12_1_g]
theorem cell10_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 0 b := complementReserve_pos_of_branches (cell10_complement0_0 hb hν) (cell10_complement0_1 hb hν)
theorem cell10_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 1 b := complementReserve_pos_of_branches (cell10_complement1_0 hb hν) (cell10_complement1_1 hb hν)
theorem cell10_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 2 b := complementReserve_pos_of_branches (cell10_complement2_0 hb hν) (cell10_complement2_1 hb hν)
theorem cell10_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 3 b := complementReserve_pos_of_branches (cell10_complement3_0 hb hν) (cell10_complement3_1 hb hν)
theorem cell10_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 4 b := complementReserve_pos_of_branches (cell10_complement4_0 hb hν) (cell10_complement4_1 hb hν)
theorem cell10_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 5 b := complementReserve_pos_of_branches (cell10_complement5_0 hb hν) (cell10_complement5_1 hb hν)
theorem cell10_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 6 b := complementReserve_pos_of_branches (cell10_complement6_0 hb hν) (cell10_complement6_1 hb hν)
theorem cell10_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 7 b := complementReserve_pos_of_branches (cell10_complement7_0 hb hν) (cell10_complement7_1 hb hν)
theorem cell10_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 8 b := complementReserve_pos_of_branches (cell10_complement8_0 hb hν) (cell10_complement8_1 hb hν)
theorem cell10_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 9 b := complementReserve_pos_of_branches (cell10_complement9_0 hb hν) (cell10_complement9_1 hb hν)
theorem cell10_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 10 b := complementReserve_pos_of_branches (cell10_complement10_0 hb hν) (cell10_complement10_1 hb hν)
theorem cell10_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 11 b := complementReserve_pos_of_branches (cell10_complement11_0 hb hν) (cell10_complement11_1 hb hν)
theorem cell10_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell10 12 b := complementReserve_pos_of_branches (cell10_complement12_0 hb hν) (cell10_complement12_1 hb hν)
theorem cell10_all_domains {b : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell10 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell10_domain0_0 (ν := (6239/10000:ℝ)) hb (by norm_num)
   | true => exact cell10_domain0_1 (ν := (6239/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell10_domain1_0 (ν := (6239/10000:ℝ)) hb (by norm_num)
   | true => exact cell10_domain1_1 (ν := (6239/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell10_domain2_0 (ν := (6239/10000:ℝ)) hb (by norm_num)
   | true => exact cell10_domain2_1 (ν := (6239/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell10_domain3_0 (ν := (6239/10000:ℝ)) hb (by norm_num)
   | true => exact cell10_domain3_1 (ν := (6239/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell10_domain4_0 (ν := (6239/10000:ℝ)) hb (by norm_num)
   | true => exact cell10_domain4_1 (ν := (6239/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell10_domain5_0 (ν := (6239/10000:ℝ)) hb (by norm_num)
   | true => exact cell10_domain5_1 (ν := (6239/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell10_domain6_0 (ν := (6239/10000:ℝ)) hb (by norm_num)
   | true => exact cell10_domain6_1 (ν := (6239/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell10_domain7_0 (ν := (6239/10000:ℝ)) hb (by norm_num)
   | true => exact cell10_domain7_1 (ν := (6239/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell10_domain8_0 (ν := (6239/10000:ℝ)) hb (by norm_num)
   | true => exact cell10_domain8_1 (ν := (6239/10000:ℝ)) hb (by norm_num)
end
end Record12518109Admission
