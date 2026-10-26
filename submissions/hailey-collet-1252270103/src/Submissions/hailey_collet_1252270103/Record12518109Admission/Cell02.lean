/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell2 : Cell := ⟨(306003/312500:ℝ), (74001/20000:ℝ), (399/625:ℝ), (17/500:ℝ), (9/250:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (481/100000:ℝ), (1/25:ℝ)⟩
def cell2_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(36938107776057079238364081471638935426783/963650741243898278552745937500000:ℝ), (5519439270890942228623232482396361183003861/1927301482487796557105491875000000:ℝ), (10557366402032726041372534099761258649538861/1284867654991864371403661250000000:ℝ), (61000476750557905612779958648754061171202319/7709205929951186228421967500000000:ℝ), (38967302921200622086799651593071546088530847/15418411859902372456843935000000000:ℝ)],
  ![(35391093435763670503520151305363803426783/963650741243898278552745937500000:ℝ), (5361076935882242885297927499893024933003861/1927301482487796557105491875000000:ℝ), (10266680547316991296760840481919852399538861/1284867654991864371403661250000000:ℝ), (59368982098540361945687673844554842421202319/7709205929951186228421967500000000:ℝ), (37949087574380599048844368695122327338530847/15418411859902372456843935000000000:ℝ)]]
theorem cell2_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highRegular cell2 2 b ν := by
 have heq : highRegular cell2 2 b ν = Record12518109.Bernstein.bsum 1 4 (35391093435763670503520151305363803426783/3106224821156170654296875000000000000000:ℝ) cell2_regular2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_regular2_g]
def cell2_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(20874666553806823113155153206987009492783/963650741243898278552745937500000:ℝ), (5291938025492120768142447517259045939225861/1927301482487796557105491875000000:ℝ), (10289132726289234963488311315270691088260861/1284867654991864371403661250000000:ℝ), (60013979257675195508662473521309163582340319/7709205929951186228421967500000000:ℝ), (38630923674000343113986409886365942997224847/15418411859902372456843935000000000:ℝ)],
  ![(4888277625568427809737267766791877492783/963650741243898278552745937500000:ℝ), (5038659553389511110832648513955709689225861/1927301482487796557105491875000000:ℝ), (9923160645115335943562100728679284838260861/1284867654991864371403661250000000:ℝ), (58153478842844874926805423092109944832340319/7709205929951186228421967500000000:ℝ), (37530408119926379868279662144666724247224847/15418411859902372456843935000000000:ℝ)]]
theorem cell2_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highRegular cell2 3 b ν := by
 have heq : highRegular cell2 3 b ν = Record12518109.Bernstein.bsum 1 4 (4888277625568427809737267766791877492783/3106224821156170654296875000000000000000:ℝ) cell2_regular3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_regular3_g]
def cell2_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(319554738339523149671268364633757877520783/963650741243898278552745937500000:ℝ), (6188934808293869478234115646344074497501861/1927301482487796557105491875000000:ℝ), (9934010545319123068402992665727296331536861/1284867654991864371403661250000000:ℝ), (54870981433007611406786893427970714242944319/7709205929951186228421967500000000:ℝ), (34956652158360887872054464597245058171276847/15418411859902372456843935000000000:ℝ)],
  ![(270688678379289625116518959153802745520783/963650741243898278552745937500000:ℝ), (5720980961784404892313138219765738247501861/1927301482487796557105491875000000:ℝ), (9399493977849029133772857969760890081536861/1284867654991864371403661250000000:ℝ), (52504753122502260947541747295646495492944319/7709205929951186228421967500000000:ℝ), (33676763200457410301097472714920839421276847/15418411859902372456843935000000000:ℝ)]]
theorem cell2_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highRegular cell2 4 b ν := by
 have heq : highRegular cell2 4 b ν = Record12518109.Bernstein.bsum 1 4 (270688678379289625116518959153802745520783/3106224821156170654296875000000000000000:ℝ) cell2_regular4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_regular4_g]
def cell2_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(61546344386347784807967005544094951/3763438616386545351165000000000:ℝ), (332411455441893562581599156222450821/7526877232773090702330000000000:ℝ), (424163017013837393269024556597042071/15053754465546181404660000000000:ℝ)],
  ![(59613920594455323232341929740094951/3763438616386545351165000000000:ℝ), (323801932732290123474917244972450821/7526877232773090702330000000000:ℝ), (414634130740862342479628462847042071/15053754465546181404660000000000:ℝ)]]
theorem cell2_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 0 false b ν := by
 have heq : highBranch cell2 0 false b ν = Record12518109.Bernstein.bsum 1 2 (59613920594455323232341929740094951/151086775301036140625000000000000000:ℝ) cell2_exceptional0_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional0_0_g]
def cell2_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(2304470422610241147136462788798293348333/141064969658016879397717695000000000:ℝ), (12450461904566001586897638808823999123543/282129939316033758795435390000000000:ℝ), (15890153823297608856488220647246748747293/564259878632067517590870780000000000:ℝ)],
  ![(744080415861009763088691914958987116111/47021656552672293132572565000000000:ℝ), (1347615798423281707946913038813361013727/31347771035114862088381710000000000:ℝ), (5177916385735236965198296471738499582431/188086626210689172530290260000000000:ℝ)]]
theorem cell2_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 0 true b ν := by
 have heq : highBranch cell2 0 true b ν = Record12518109.Bernstein.bsum 1 2 (2232241247583029289266075744876961348333/5663185598608737659046875000000000000000:ℝ) cell2_exceptional0_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional0_1_g]
theorem cell2_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell2 0 b ν :=
 highExceptional_pos_of_branches (cell2_exceptional0_0 hb hν) (cell2_exceptional0_1 hb hν)
def cell2_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(1015273767674344003594875114557629/198075716651923439535000000000:ℝ), (24584073279210082151244424834076359/396151433303846879070000000000:ℝ), (45397866418009178147987994806160109/792302866607693758140000000000:ℝ)],
  ![(30864573192346466055081793501859/6389539246836239985000000000:ℝ), (778934913729750410586602776905689/12779078493672479970000000000:ℝ), (1443725537498439894914103663101939/25558156987344959940000000000:ℝ)]]
theorem cell2_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 1 false b ν := by
 have heq : highBranch cell2 1 false b ν = Record12518109.Bernstein.bsum 1 2 (956801768962740447707535598557629/7951935542159796875000000000000000:ℝ) cell2_exceptional1_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional1_0_g]
def cell2_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(37925443264093600980401204971015307807/7424472087264046284090405000000000:ℝ), (920994467158184413519913599010309164397/14848944174528092568180810000000000:ℝ), (1701187777291919174236053651020342565647/29697888349056185136361620000000000:ℝ)],
  ![(11914822374660316006582680217595769269/2474824029088015428030135000000000:ℝ), (100516957736373046060130289107117684933/1649882686058676952020090000000000:ℝ), (559049996847996263380323955808864188549/9899296116352061712120540000000000:ℝ)]]
theorem cell2_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 1 true b ν := by
 have heq : highBranch cell2 1 true b ν = Record12518109.Bernstein.bsum 1 2 (35744467123980948019748040652787307807/298062399926775666265625000000000000000:ℝ) cell2_exceptional1_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional1_1_g]
theorem cell2_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell2 1 b ν :=
 highExceptional_pos_of_branches (cell2_exceptional1_0 hb hν) (cell2_exceptional1_1 hb hν)
def cell2_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(40581522384431522258262316053667439/1584605733215387516280000000000:ℝ), (44199566701001071761425067449957/1267684586572310013024000000:ℝ), (41011842684913259506322799233/4056590677031392041676800:ℝ)],
  ![(39719184473014415850978199925667439/1584605733215387516280000000000:ℝ), (43017667059877882762883903449957/1267684586572310013024000000:ℝ), (39407329709877747109390799233/4056590677031392041676800:ℝ)]]
theorem cell2_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 2 false b ν := by
 have heq : highBranch cell2 2 false b ν = Record12518109.Bernstein.bsum 1 2 (39407329709877747109390799233/162855639903432640000000000000:ℝ) cell2_exceptional2_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional2_0_g]
def cell2_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(1520019465689984167501042244603193816037/59395776698112370272723240000000000:ℝ), (1655071664219373428249491786356999991/47516621358489896218178592000000:ℝ), (1534742886053900731548519248640619/152053188347167667898171494400:ℝ)],
  ![(495927430685697277678062527285789938679/19798592232704123424241080000000000:ℝ), (536967914851723230558585448602999997/15838873786163298739392864000000:ℝ), (163867499869951697254277835182291/16894798705240851988685721600:ℝ)]]
theorem cell2_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 2 true b ν := by
 have heq : highBranch cell2 2 true b ν = Record12518109.Bernstein.bsum 1 2 (1474807498829565275288500516640619/6104317950500365645120000000000000:ℝ) cell2_exceptional2_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional2_1_g]
theorem cell2_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell2 2 b ν :=
 highExceptional_pos_of_branches (cell2_exceptional2_0 hb hν) (cell2_exceptional2_1 hb hν)
def cell2_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(17471040946278782254232468514698317/1254479538795515117055000000000:ℝ), (96506421452709730854809185407483607/2508959077591030234110000000000:ℝ), (125070865375221776347950985532347357/5017918155182060468220000000000:ℝ)],
  ![(50480699046943885187072329740094951/3763438616386545351165000000000:ℝ), (280909741648525753457745644972450821/7526877232773090702330000000000:ℝ), (365683709852690278254456862847042071/15053754465546181404660000000000:ℝ)]]
theorem cell2_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 3 false b ν := by
 have heq : highBranch cell2 3 false b ν = Record12518109.Bernstein.bsum 1 2 (50480699046943885187072329740094951/151086775301036140625000000000000000:ℝ) cell2_exceptional3_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional3_0_g]
def cell2_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(1962129879344869914885622371998293348333/141064969658016879397717695000000000:ℝ), (10842733906173261705543995726023999123543/282129939316033758795435390000000000:ℝ), (14055345197146255373136113564446748747293/564259878632067517590870780000000000:ℝ)],
  ![(1889900704317658057015235328076961348333/141064969658016879397717695000000000:ℝ), (10520814187416795490168574266520249123543/282129939316033758795435390000000000:ℝ), (13698940531054357412242782332415498747293/564259878632067517590870780000000000:ℝ)]]
theorem cell2_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 3 true b ν := by
 have heq : highBranch cell2 3 true b ν = Record12518109.Bernstein.bsum 1 2 (1889900704317658057015235328076961348333/5663185598608737659046875000000000000000:ℝ) cell2_exceptional3_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional3_1_g]
theorem cell2_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell2 3 b ν :=
 highExceptional_pos_of_branches (cell2_exceptional3_0 hb hν) (cell2_exceptional3_1 hb hν)
def cell2_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(208381527752321218027991704852543/66025238883974479845000000000:ℝ), (7343843625684290071221008278025453/132050477767948959690000000000:ℝ), (1550709052173941835038207215042967/29344550615099768820000000000:ℝ)],
  ![(566672584545360098196635598557629/198075716651923439535000000000:ℝ), (21594439923465050790603286084076359/396151433303846879070000000000:ℝ), (41226769653138888140380813556160109/792302866607693758140000000000:ℝ)]]
theorem cell2_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 4 false b ν := by
 have heq : highBranch cell2 4 false b ν = Record12518109.Bernstein.bsum 1 2 (566672584545360098196635598557629/7951935542159796875000000000000000:ℝ) cell2_exceptional4_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional4_0_g]
def cell2_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(23302231044576933339684140271015307807/7424472087264046284090405000000000:ℝ), (825317520298125638463549982810309164397/14848944174528092568180810000000000:ℝ), (1568920690216849418388921909820342565647/29697888349056185136361620000000000:ℝ)],
  ![(21121254904464280379030975952787307807/7424472087264046284090405000000000:ℝ), (808975672767298639484808985764059164397/14848944174528092568180810000000000:ℝ), (1544882903468919034293840126226592565647/29697888349056185136361620000000000:ℝ)]]
theorem cell2_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 4 true b ν := by
 have heq : highBranch cell2 4 true b ν = Record12518109.Bernstein.bsum 1 2 (21121254904464280379030975952787307807/298062399926775666265625000000000000000:ℝ) cell2_exceptional4_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional4_1_g]
theorem cell2_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell2 4 b ν :=
 highExceptional_pos_of_branches (cell2_exceptional4_0 hb hν) (cell2_exceptional4_1 hb hν)
def cell2_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(3089846593017171424666403034557629/198075716651923439535000000000:ℝ), (31924428467712728659572348793183319393/921844385298051687595890000000000:ℝ), (36661983416411368663599259501144573643/1843688770596103375191780000000000:ℝ)],
  ![(2991045075307360580279063518557629/198075716651923439535000000000:ℝ), (30969625477153293704096568171933319393/921844385298051687595890000000000:ℝ), (35658378480864129867618297782394573643/1843688770596103375191780000000000:ℝ)]]
theorem cell2_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 5 false b ν := by
 have heq : highBranch cell2 5 false b ν = Record12518109.Bernstein.bsum 1 2 (2991045075307360580279063518557629/7951935542159796875000000000000000:ℝ) cell2_exceptional5_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional5_0_g]
def cell2_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(115686656476418801204425285996375307807/7424472087264046284090405000000000:ℝ), (1195482304160153816524443750830302735807819/34553493094126871406156744870000000000:ℝ), (1373129658051747367004541750119729580260569/69106986188253742812313489740000000000:ℝ)],
  ![(37331336325232114816308873892715769269/2474824029088015428030135000000000:ℝ), (128865589213022689035667599793780998423091/3839277010458541267350749430000000000:ℝ), (445201806631360355851889070388607776753523/23035662062751247604104496580000000000:ℝ)]]
theorem cell2_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 5 true b ν := by
 have heq : highBranch cell2 5 true b ν = Record12518109.Bernstein.bsum 1 2 (111994008975696344448926621678147307807/298062399926775666265625000000000000000:ℝ) cell2_exceptional5_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional5_1_g]
theorem cell2_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell2 5 b ν :=
 highExceptional_pos_of_branches (cell2_exceptional5_0 hb hν) (cell2_exceptional5_1 hb hν)
def cell2_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(40581522384431522258262316053667439/1584605733215387516280000000000:ℝ), (44199566701001071761425067449957/1267684586572310013024000000:ℝ), (41011842684913259506322799233/4056590677031392041676800:ℝ)],
  ![(39719184473014415850978199925667439/1584605733215387516280000000000:ℝ), (43017667059877882762883903449957/1267684586572310013024000000:ℝ), (39407329709877747109390799233/4056590677031392041676800:ℝ)]]
theorem cell2_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 6 false b ν := by
 have heq : highBranch cell2 6 false b ν = Record12518109.Bernstein.bsum 1 2 (39407329709877747109390799233/162855639903432640000000000000:ℝ) cell2_exceptional6_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional6_0_g]
def cell2_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(1520019465689984167501042244603193816037/59395776698112370272723240000000000:ℝ), (1655071664219373428249491786356999991/47516621358489896218178592000000:ℝ), (1534742886053900731548519248640619/152053188347167667898171494400:ℝ)],
  ![(495927430685697277678062527285789938679/19798592232704123424241080000000000:ℝ), (536967914851723230558585448602999997/15838873786163298739392864000000:ℝ), (163867499869951697254277835182291/16894798705240851988685721600:ℝ)]]
theorem cell2_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 6 true b ν := by
 have heq : highBranch cell2 6 true b ν = Record12518109.Bernstein.bsum 1 2 (1474807498829565275288500516640619/6104317950500365645120000000000000:ℝ) cell2_exceptional6_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional6_1_g]
theorem cell2_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell2 6 b ν :=
 highExceptional_pos_of_branches (cell2_exceptional6_0 hb hν) (cell2_exceptional6_1 hb hν)
def cell2_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(2615236045399885393155503034557629/198075716651923439535000000000:ℝ), (27032056170640614774476973793183319393/921844385298051687595890000000000:ℝ), (31294913799488839274711966701144573643/1843688770596103375191780000000000:ℝ)],
  ![(2516434527690074548768163518557629/198075716651923439535000000000:ℝ), (26077253180081179819001193171933319393/921844385298051687595890000000000:ℝ), (30291308863941600478731004982394573643/1843688770596103375191780000000000:ℝ)]]
theorem cell2_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 7 false b ν := by
 have heq : highBranch cell2 7 false b ν = Record12518109.Bernstein.bsum 1 2 (2516434527690074548768163518557629/7951935542159796875000000000000000:ℝ) cell2_exceptional7_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional7_0_g]
def cell2_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(97896829320080068885302221296375307807/7424472087264046284090405000000000:ℝ), (1012101513348999771769413809705302735807819/34553493094126871406156744870000000000:ℝ), (1171955787600640197920879354097329580260569/69106986188253742812313489740000000000:ℝ)],
  ![(3489043771087318967770502110301752141/274980447676446158670015000000000:ℝ), (108489945789561128507330939668780998423091/3839277010458541267350749430000000000:ℝ), (126047949938108210941333868349269258917841/7678554020917082534701498860000000000:ℝ)]]
theorem cell2_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell2 7 true b ν := by
 have heq : highBranch cell2 7 true b ν = Record12518109.Bernstein.bsum 1 2 (94204181819357612129803556978147307807/298062399926775666265625000000000000000:ℝ) cell2_exceptional7_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_exceptional7_1_g]
theorem cell2_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell2 7 b ν :=
 highExceptional_pos_of_branches (cell2_exceptional7_0 hb hν) (cell2_exceptional7_1 hb hν)
def cell2_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(20215822497217060054830663/9537996797656821320500000000:ℝ)],
  ![(158545701238727047231230663/9537996797656821320500000000:ℝ)]]
theorem cell2_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 0 false b := by
 have heq : domainBranch cell2 0 false b = Record12518109.Bernstein.bsum 1 0 (20215822497217060054830663/4768998398828410660250000000000:ℝ) cell2_domain0_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain0_0_g]
def cell2_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(20215822497217060054830663/9537996797656821320500000000:ℝ)],
  ![(158545701238727047231230663/9537996797656821320500000000:ℝ)]]
theorem cell2_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 0 true b := by
 have heq : domainBranch cell2 0 true b = Record12518109.Bernstein.bsum 1 0 (20215822497217060054830663/4768998398828410660250000000000:ℝ) cell2_domain0_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain0_1_g]
def cell2_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(3368117101221535609110534994373/1272309686745567500000000000000:ℝ)],
  ![(2661017062247833943696916244373/1272309686745567500000000000000:ℝ)]]
theorem cell2_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 1 false b := by
 have heq : domainBranch cell2 1 false b = Record12518109.Bernstein.bsum 1 0 (2661017062247833943696916244373/636154843372783750000000000000000:ℝ) cell2_domain1_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain1_0_g]
def cell2_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(51496018434343342821294147374991/10178477493964540000000000000000:ℝ)],
  ![(45839218122553729497985197374991/10178477493964540000000000000000:ℝ)]]
theorem cell2_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 1 true b := by
 have heq : domainBranch cell2 1 true b = Record12518109.Bernstein.bsum 1 0 (45839218122553729497985197374991/5089238746982270000000000000000000:ℝ) cell2_domain1_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain1_1_g]
def cell2_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(430350959727149897396946963443/63615484337278375000000000000:ℝ)],
  ![(452733093933439439022875088443/63615484337278375000000000000:ℝ)]]
theorem cell2_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 2 false b := by
 have heq : domainBranch cell2 2 false b = Record12518109.Bernstein.bsum 1 0 (430350959727149897396946963443/31807742168639187500000000000000:ℝ) cell2_domain2_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain2_0_g]
def cell2_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(4548148937436302254341394830987/1017847749396454000000000000000:ℝ)],
  ![(4906263084736934920356244830987/1017847749396454000000000000000:ℝ)]]
theorem cell2_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 2 true b := by
 have heq : domainBranch cell2 2 true b = Record12518109.Bernstein.bsum 1 0 (4548148937436302254341394830987/508923874698227000000000000000000:ℝ) cell2_domain2_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain2_1_g]
def cell2_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(5280847372766031371876846027/10178477493964540000000000000:ℝ)],
  ![(57190786265567090083506846027/10178477493964540000000000000:ℝ)]]
theorem cell2_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 3 false b := by
 have heq : domainBranch cell2 3 false b = Record12518109.Bernstein.bsum 1 0 (5280847372766031371876846027/5089238746982270000000000000000:ℝ) cell2_domain3_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain3_0_g]
def cell2_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(5280847372766031371876846027/10178477493964540000000000000:ℝ)],
  ![(57190786265567090083506846027/10178477493964540000000000000:ℝ)]]
theorem cell2_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 3 true b := by
 have heq : domainBranch cell2 3 true b = Record12518109.Bernstein.bsum 1 0 (5280847372766031371876846027/5089238746982270000000000000000:ℝ) cell2_domain3_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain3_1_g]
def cell2_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(928067403032459400193869/127230968674556750000000:ℝ)],
  ![(636528711479153700193869/127230968674556750000000:ℝ)]]
theorem cell2_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 4 false b := by
 have heq : domainBranch cell2 4 false b = Record12518109.Bernstein.bsum 1 0 (636528711479153700193869/63615484337278375000000000:ℝ) cell2_domain4_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain4_0_g]
def cell2_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(928067403032459400193869/127230968674556750000000:ℝ)],
  ![(636528711479153700193869/127230968674556750000000:ℝ)]]
theorem cell2_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 4 true b := by
 have heq : domainBranch cell2 4 true b = Record12518109.Bernstein.bsum 1 0 (636528711479153700193869/63615484337278375000000000:ℝ) cell2_domain4_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain4_1_g]
def cell2_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(284030459576947399704539456219/127230968674556750000000000000:ℝ)],
  ![(214351567901746142554776956219/127230968674556750000000000000:ℝ)]]
theorem cell2_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 5 false b := by
 have heq : domainBranch cell2 5 false b = Record12518109.Bernstein.bsum 1 0 (214351567901746142554776956219/63615484337278375000000000000000:ℝ) cell2_domain5_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain5_0_g]
def cell2_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(2361338313026520507443968819149/508923874698227000000000000000:ℝ)],
  ![(2082622746325715478844918819149/508923874698227000000000000000:ℝ)]]
theorem cell2_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 5 true b := by
 have heq : domainBranch cell2 5 true b = Record12518109.Bernstein.bsum 1 0 (2082622746325715478844918819149/254461937349113500000000000000000:ℝ) cell2_domain5_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain5_1_g]
def cell2_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(21785430397036045829376488314350651/517624182798130539678500000000000:ℝ)],
  ![(20522521066713439477691535889350651/517624182798130539678500000000000:ℝ)]]
theorem cell2_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 6 false b := by
 have heq : domainBranch cell2 6 false b = Record12518109.Bernstein.bsum 1 0 (20522521066713439477691535889350651/258812091399065269839250000000000000:ℝ) cell2_domain6_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain6_0_g]
def cell2_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(42602192064663070168598598266227623/1035248365596261079357000000000000:ℝ)],
  ![(40076373404017857465228693416227623/1035248365596261079357000000000000:ℝ)]]
theorem cell2_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 6 true b := by
 have heq : domainBranch cell2 6 true b = Record12518109.Bernstein.bsum 1 0 (40076373404017857465228693416227623/517624182798130539678500000000000000:ℝ) cell2_domain6_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain6_1_g]
def cell2_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(293273875709134258682746227/40713909975858160000000000:ℝ)],
  ![(520119039320175043128346227/40713909975858160000000000:ℝ)]]
theorem cell2_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 7 false b := by
 have heq : domainBranch cell2 7 false b = Record12518109.Bernstein.bsum 1 0 (293273875709134258682746227/20356954987929080000000000000:ℝ) cell2_domain7_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain7_0_g]
def cell2_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(293273875709134258682746227/40713909975858160000000000:ℝ)],
  ![(520119039320175043128346227/40713909975858160000000000:ℝ)]]
theorem cell2_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 7 true b := by
 have heq : domainBranch cell2 7 true b = Record12518109.Bernstein.bsum 1 0 (293273875709134258682746227/20356954987929080000000000000:ℝ) cell2_domain7_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain7_1_g]
def cell2_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(134940235671192930537666618971/6361548433727837500000000000:ℝ)],
  ![(124536817158736252592147868971/6361548433727837500000000000:ℝ)]]
theorem cell2_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 8 false b := by
 have heq : domainBranch cell2 8 false b = Record12518109.Bernstein.bsum 1 0 (124536817158736252592147868971/3180774216863918750000000000000:ℝ) cell2_domain8_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain8_0_g]
def cell2_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(1126692500393322187653430593807/50892387469822700000000000000:ℝ)],
  ![(1043465152293668764089280593807/50892387469822700000000000000:ℝ)]]
theorem cell2_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell2 8 true b := by
 have heq : domainBranch cell2 8 true b = Record12518109.Bernstein.bsum 1 0 (1043465152293668764089280593807/25446193734911350000000000000000:ℝ) cell2_domain8_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_domain8_1_g]
def cell2_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(1851438198962726592087/1628556399034326400000:ℝ)],
  ![(3147165716977418592087/1628556399034326400000:ℝ)]]
theorem cell2_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell2 0 b := by
 have heq : ordinary cell2 0 b = Record12518109.Bernstein.bsum 1 0 (1851438198962726592087/814278199517163200000000:ℝ) cell2_ordinary0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordinary0_g]
def cell2_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(12674840670477122223739/4885669197102979200000:ℝ)],
  ![(8787658116433046223739/4885669197102979200000:ℝ)]]
theorem cell2_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell2 1 b := by
 have heq : ordinary cell2 1 b = Record12518109.Bernstein.bsum 1 0 (8787658116433046223739/2442834598551489600000000:ℝ) cell2_ordinary1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordinary1_g]
def cell2_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(310905714068981741387203/1272309686745567500000:ℝ)],
  ![(304831991328287872637203/1272309686745567500000:ℝ)]]
theorem cell2_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell2 2 b := by
 have heq : ordinary cell2 2 b = Record12518109.Bernstein.bsum 1 0 (304831991328287872637203/636154843372783750000000:ℝ) cell2_ordinary2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordinary2_g]
def cell2_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(339999989/40000000:ℝ)],
  ![(379999989/40000000:ℝ)]]
theorem cell2_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell2 3 b := by
 have heq : ordinary cell2 3 b = Record12518109.Bernstein.bsum 1 0 (339999989/20000000000:ℝ) cell2_ordinary3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordinary3_g]
def cell2_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(2336629697433076272128121/10178477493964540000000:ℝ)],
  ![(2267682960519596242128121/10178477493964540000000:ℝ)]]
theorem cell2_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell2 4 b := by
 have heq : ordinary cell2 4 b = Record12518109.Bernstein.bsum 1 0 (2267682960519596242128121/5089238746982270000000000:ℝ) cell2_ordinary4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordinary4_g]
def cell2_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(942144968021336909/381237906265000000000000:ℝ)],
  ![(942144968021336909/381237906265000000000000:ℝ)]]
theorem cell2_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell2 5 b := by
 have heq : ordinary cell2 5 b = Record12518109.Bernstein.bsum 1 0 (942144968021336909/190618953132500000000000000:ℝ) cell2_ordinary5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordinary5_g]
def cell2_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(1851397485052750733927/1628556399034326400000:ℝ)],
  ![(3147125003067442733927/1628556399034326400000:ℝ)]]
theorem cell2_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 0 false b := by
 have heq : complementBranch cell2 0 false b = Record12518109.Bernstein.bsum 1 0 (1851397485052750733927/814278199517163200000000:ℝ) cell2_complement0_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement0_0_g]
def cell2_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(41228951211892796394610264009/38151987190627285282000000000:ℝ)],
  ![(71768237648805247358345464009/38151987190627285282000000000:ℝ)]]
theorem cell2_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 0 true b := by
 have heq : complementBranch cell2 0 true b = Record12518109.Bernstein.bsum 1 0 (41228951211892796394610264009/19075993595313642641000000000000:ℝ) cell2_complement0_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement0_1_g]
def cell2_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(940603499029999349671628773/40713909975858160000000000:ℝ)],
  ![(888567151908478674579628773/40713909975858160000000000:ℝ)]]
theorem cell2_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 1 false b := by
 have heq : complementBranch cell2 1 false b = Record12518109.Bernstein.bsum 1 0 (888567151908478674579628773/20356954987929080000000000000:ℝ) cell2_complement1_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement1_0_g]
def cell2_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(35167211907544930819206724333719/1526079487625091411280000000000:ℝ)],
  ![(33224111101921851887382696333719/1526079487625091411280000000000:ℝ)]]
theorem cell2_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 1 true b := by
 have heq : complementBranch cell2 1 true b = Record12518109.Bernstein.bsum 1 0 (33224111101921851887382696333719/763039743812545705640000000000000:ℝ) cell2_complement1_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement1_1_g]
def cell2_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(820246055034461290462928773/40713909975858160000000000:ℝ)],
  ![(638636956111471415370928773/40713909975858160000000000:ℝ)]]
theorem cell2_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 2 false b := by
 have heq : complementBranch cell2 2 false b = Record12518109.Bernstein.bsum 1 0 (638636956111471415370928773/20356954987929080000000000000:ℝ) cell2_complement2_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement2_0_g]
def cell2_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(30655853834260177745887022233719/1526079487625091411280000000000:ℝ)],
  ![(23855977572862628790462994233719/1526079487625091411280000000000:ℝ)]]
theorem cell2_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 2 true b := by
 have heq : complementBranch cell2 2 true b = Record12518109.Bernstein.bsum 1 0 (23855977572862628790462994233719/763039743812545705640000000000000:ℝ) cell2_complement2_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement2_1_g]
def cell2_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(767123310149593064473803773/40713909975858160000000000:ℝ)],
  ![(747480150978439689381803773/40713909975858160000000000:ℝ)]]
theorem cell2_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 3 false b := by
 have heq : complementBranch cell2 3 false b = Record12518109.Bernstein.bsum 1 0 (747480150978439689381803773/20356954987929080000000000000:ℝ) cell2_complement3_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement3_0_g]
def cell2_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(28664653987740662031136649858719/1526079487625091411280000000000:ℝ)],
  ![(27935747046061200605212621858719/1526079487625091411280000000000:ℝ)]]
theorem cell2_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 3 true b := by
 have heq : complementBranch cell2 3 true b = Record12518109.Bernstein.bsum 1 0 (27935747046061200605212621858719/763039743812545705640000000000000:ℝ) cell2_complement3_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement3_1_g]
def cell2_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(752078629650150807072716273/40713909975858160000000000:ℝ)],
  ![(716238876503813781980716273/40713909975858160000000000:ℝ)]]
theorem cell2_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 4 false b := by
 have heq : complementBranch cell2 4 false b = Record12518109.Bernstein.bsum 1 0 (716238876503813781980716273/20356954987929080000000000000:ℝ) cell2_complement4_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement4_0_g]
def cell2_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(28100734228580067896971687096219/1526079487625091411280000000000:ℝ)],
  ![(26764730354928797718097659096219/1526079487625091411280000000000:ℝ)]]
theorem cell2_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 4 true b := by
 have heq : complementBranch cell2 4 true b = Record12518109.Bernstein.bsum 1 0 (26764730354928797718097659096219/763039743812545705640000000000000:ℝ) cell2_complement4_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement4_1_g]
def cell2_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(5303259/200000:ℝ)],
  ![(4403667/200000:ℝ)]]
theorem cell2_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 5 false b := by
 have heq : complementBranch cell2 5 false b = Record12518109.Bernstein.bsum 1 0 (4403667/100000000:ℝ) cell2_complement5_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement5_0_g]
def cell2_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(252353405254495240368324191471/9537996797656821320500000000:ℝ)],
  ![(209497987138087267670626811471/9537996797656821320500000000:ℝ)]]
theorem cell2_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 5 true b := by
 have heq : complementBranch cell2 5 true b = Record12518109.Bernstein.bsum 1 0 (209497987138087267670626811471/4768998398828410660250000000000:ℝ) cell2_complement5_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement5_1_g]
def cell2_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(93359713146047759997231/1628556399034326400000:ℝ)],
  ![(84289620519944915997231/1628556399034326400000:ℝ)]]
theorem cell2_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 6 false b := by
 have heq : complementBranch cell2 6 false b = Record12518109.Bernstein.bsum 1 0 (84289620519944915997231/814278199517163200000000:ℝ) cell2_complement6_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement6_0_g]
def cell2_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(2184890603743404247371757559009/38151987190627285282000000000:ℝ)],
  ![(1972591117391593197155492759009/38151987190627285282000000000:ℝ)]]
theorem cell2_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 6 true b := by
 have heq : complementBranch cell2 6 true b = Record12518109.Bernstein.bsum 1 0 (1972591117391593197155492759009/19075993595313642641000000000000:ℝ) cell2_complement6_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement6_1_g]
def cell2_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(73629054241257088273028773/244283459855148960000000000:ℝ)],
  ![(138239525807171253181028773/244283459855148960000000000:ℝ)]]
theorem cell2_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 7 false b := by
 have heq : complementBranch cell2 7 false b = Record12518109.Bernstein.bsum 1 0 (73629054241257088273028773/122141729927574480000000000000:ℝ) cell2_complement7_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement7_0_g]
def cell2_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(2245396341144472210476539710519/9156476925750548467680000000000:ℝ)],
  ![(4711456208046916049619551710519/9156476925750548467680000000000:ℝ)]]
theorem cell2_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 7 true b := by
 have heq : complementBranch cell2 7 true b = Record12518109.Bernstein.bsum 1 0 (2245396341144472210476539710519/4578238462875274233840000000000000:ℝ) cell2_complement7_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement7_1_g]
def cell2_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(1184491973618893043525228773/244283459855148960000000000:ℝ)],
  ![(2026538955993622408433228773/244283459855148960000000000:ℝ)]]
theorem cell2_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 8 false b := by
 have heq : complementBranch cell2 8 false b = Record12518109.Bernstein.bsum 1 0 (1184491973618893043525228773/122141729927574480000000000000:ℝ) cell2_complement8_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement8_0_g]
def cell2_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(43883871148176400721194752310519/9156476925750548467680000000000:ℝ)],
  ![(75490583749725664701937764310519/9156476925750548467680000000000:ℝ)]]
theorem cell2_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 8 true b := by
 have heq : complementBranch cell2 8 true b = Record12518109.Bernstein.bsum 1 0 (43883871148176400721194752310519/4578238462875274233840000000000000:ℝ) cell2_complement8_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement8_1_g]
def cell2_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(1462207703463302032338278773/244283459855148960000000000:ℝ)],
  ![(2498613813540235197246278773/244283459855148960000000000:ℝ)]]
theorem cell2_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 9 false b := by
 have heq : complementBranch cell2 9 false b = Record12518109.Bernstein.bsum 1 0 (1462207703463302032338278773/122141729927574480000000000000:ℝ) cell2_complement9_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement9_0_g]
def cell2_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(54293489849934382848874305460519/9156476925750548467680000000000:ℝ)],
  ![(93185365635145351865017317460519/9156476925750548467680000000000:ℝ)]]
theorem cell2_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 9 true b := by
 have heq : complementBranch cell2 9 true b = Record12518109.Bernstein.bsum 1 0 (54293489849934382848874305460519/4578238462875274233840000000000000:ℝ) cell2_complement9_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement9_1_g]
def cell2_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(1851397485052750733927/1628556399034326400000:ℝ)],
  ![(3147125003067442733927/1628556399034326400000:ℝ)]]
theorem cell2_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 10 false b := by
 have heq : complementBranch cell2 10 false b = Record12518109.Bernstein.bsum 1 0 (1851397485052750733927/814278199517163200000000:ℝ) cell2_complement10_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement10_0_g]
def cell2_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(41228951211892796394610264009/38151987190627285282000000000:ℝ)],
  ![(71768237648805247358345464009/38151987190627285282000000000:ℝ)]]
theorem cell2_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 10 true b := by
 have heq : complementBranch cell2 10 true b = Record12518109.Bernstein.bsum 1 0 (41228951211892796394610264009/19075993595313642641000000000000:ℝ) cell2_complement10_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement10_1_g]
def cell2_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(5554294239933191847181/814278199517163200000:ℝ)],
  ![(9441476793977267847181/814278199517163200000:ℝ)]]
theorem cell2_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 11 false b := by
 have heq : complementBranch cell2 11 false b = Record12518109.Bernstein.bsum 1 0 (5554294239933191847181/407139099758581600000000:ℝ) cell2_complement11_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement11_0_g]
def cell2_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(129048003749258712027300477317/19075993595313642641000000000:ℝ)],
  ![(220204763464191031627918077317/19075993595313642641000000000:ℝ)]]
theorem cell2_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 11 true b := by
 have heq : complementBranch cell2 11 true b = Record12518109.Bernstein.bsum 1 0 (129048003749258712027300477317/9537996797656821320500000000000:ℝ) cell2_complement11_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement11_1_g]
def cell2_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(12960026678829110286449/1628556399034326400000:ℝ)],
  ![(22030119304931954286449/1628556399034326400000:ℝ)]]
theorem cell2_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 12 false b := by
 have heq : complementBranch cell2 12 false b = Record12518109.Bernstein.bsum 1 0 (12960026678829110286449/814278199517163200000000:ℝ) cell2_complement12_0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement12_0_g]
def cell2_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(301469418755842349586599092759/38151987190627285282000000000:ℝ)],
  ![(514137784784297426435334292759/38151987190627285282000000000:ℝ)]]
theorem cell2_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell2 12 true b := by
 have heq : complementBranch cell2 12 true b = Record12518109.Bernstein.bsum 1 0 (301469418755842349586599092759/19075993595313642641000000000000:ℝ) cell2_complement12_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement12_1_g]
theorem cell2_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 0 b := complementReserve_pos_of_branches (cell2_complement0_0 hb hν) (cell2_complement0_1 hb hν)
theorem cell2_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 1 b := complementReserve_pos_of_branches (cell2_complement1_0 hb hν) (cell2_complement1_1 hb hν)
theorem cell2_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 2 b := complementReserve_pos_of_branches (cell2_complement2_0 hb hν) (cell2_complement2_1 hb hν)
theorem cell2_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 3 b := complementReserve_pos_of_branches (cell2_complement3_0 hb hν) (cell2_complement3_1 hb hν)
theorem cell2_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 4 b := complementReserve_pos_of_branches (cell2_complement4_0 hb hν) (cell2_complement4_1 hb hν)
theorem cell2_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 5 b := complementReserve_pos_of_branches (cell2_complement5_0 hb hν) (cell2_complement5_1 hb hν)
theorem cell2_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 6 b := complementReserve_pos_of_branches (cell2_complement6_0 hb hν) (cell2_complement6_1 hb hν)
theorem cell2_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 7 b := complementReserve_pos_of_branches (cell2_complement7_0 hb hν) (cell2_complement7_1 hb hν)
theorem cell2_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 8 b := complementReserve_pos_of_branches (cell2_complement8_0 hb hν) (cell2_complement8_1 hb hν)
theorem cell2_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 9 b := complementReserve_pos_of_branches (cell2_complement9_0 hb hν) (cell2_complement9_1 hb hν)
theorem cell2_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 10 b := complementReserve_pos_of_branches (cell2_complement10_0 hb hν) (cell2_complement10_1 hb hν)
theorem cell2_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 11 b := complementReserve_pos_of_branches (cell2_complement11_0 hb hν) (cell2_complement11_1 hb hν)
theorem cell2_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell2 12 b := complementReserve_pos_of_branches (cell2_complement12_0 hb hν) (cell2_complement12_1 hb hν)
theorem cell2_all_domains {b : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell2 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell2_domain0_0 (ν := (399/625:ℝ)) hb (by norm_num)
   | true => exact cell2_domain0_1 (ν := (399/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell2_domain1_0 (ν := (399/625:ℝ)) hb (by norm_num)
   | true => exact cell2_domain1_1 (ν := (399/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell2_domain2_0 (ν := (399/625:ℝ)) hb (by norm_num)
   | true => exact cell2_domain2_1 (ν := (399/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell2_domain3_0 (ν := (399/625:ℝ)) hb (by norm_num)
   | true => exact cell2_domain3_1 (ν := (399/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell2_domain4_0 (ν := (399/625:ℝ)) hb (by norm_num)
   | true => exact cell2_domain4_1 (ν := (399/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell2_domain5_0 (ν := (399/625:ℝ)) hb (by norm_num)
   | true => exact cell2_domain5_1 (ν := (399/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell2_domain6_0 (ν := (399/625:ℝ)) hb (by norm_num)
   | true => exact cell2_domain6_1 (ν := (399/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell2_domain7_0 (ν := (399/625:ℝ)) hb (by norm_num)
   | true => exact cell2_domain7_1 (ν := (399/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell2_domain8_0 (ν := (399/625:ℝ)) hb (by norm_num)
   | true => exact cell2_domain8_1 (ν := (399/625:ℝ)) hb (by norm_num)
end
end Record12518109Admission
