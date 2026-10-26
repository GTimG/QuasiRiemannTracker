/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell5 : Cell := ⟨(306003/312500:ℝ), (74001/20000:ℝ), (627/1000:ℝ), (39/1000:ℝ), (1/25:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (539/100000:ℝ), (1/25:ℝ)⟩
def cell5_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(67719612605701092589655302094675595226993/1071068069796696070145055000000000:ℝ), (1090271243578915202378817480962630743102757/267767017449174017536263750000000:ℝ), (77077751895348776960453373530515306139741/6611531295041333766327500000000:ℝ), (3000326812638982998388634573495523295398007/267767017449174017536263750000000:ℝ), (3820159472403523642728426753027066592273007/1071068069796696070145055000000000:ℝ)],
  ![(110310999060425791160950444705857609226993/1071068069796696070145055000000000:ℝ), (1117792450291037358525846111992800993102757/267767017449174017536263750000000:ℝ), (232741227811271016838412131662545918419223/19834593885124001298982500000000:ℝ), (3001305254173745765769995843354898295398007/267767017449174017536263750000000:ℝ), (3810045193144525846215476885839566592273007/1071068069796696070145055000000000:ℝ)]]
theorem cell5_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highRegular cell5 2 b ν := by
 have heq : highRegular cell5 2 b ν = Record12518109.Bernstein.bsum 1 4 (67719612605701092589655302094675595226993/4679469562387855000000000000000000000000:ℝ) cell5_regular2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_regular2_g]
def cell5_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(8707035708919809597283879267946927212993/1071068069796696070145055000000000:ℝ), (1017225971647326985343879236365648225616757/267767017449174017536263750000000:ℝ), (668920982365513988662048265787787144595669/59503781655372003896947500000000:ℝ), (2938330462457248584570301343880345713412007/267767017449174017536263750000000:ℝ), (3782530629388372094304495515900670260287007/1071068069796696070145055000000000:ℝ)],
  ![(39829188346265841823011670456968941212993/1071068069796696070145055000000000:ℝ), (1035384409070670555240012032235818475616757/267767017449174017536263750000000:ℝ), (223665840270225451595047901333595714865223/19834593885124001298982500000000:ℝ), (2933821436232864112919940113739720713412007/267767017449174017536263750000000:ℝ), (3768574967185575228873733148713170260287007/1071068069796696070145055000000000:ℝ)]]
theorem cell5_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highRegular cell5 3 b ν := by
 have heq : highRegular cell5 3 b ν = Record12518109.Bernstein.bsum 1 4 (8707035708919809597283879267946927212993/4679469562387855000000000000000000000000:ℝ) cell5_regular3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_regular3_g]
def cell5_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(432242142830470693690698376344361138600993/1071068069796696070145055000000000:ℝ), (1138415202113389313338146751577670565228757/267767017449174017536263750000000:ℝ), (625349671183492009523526232578032740799669/59503781655372003896947500000000:ℝ), (2626257336819185125240035395981494002024007/267767017449174017536263750000000:ℝ), (3373484868693326889596505848730506048899007/1071068069796696070145055000000000:ℝ)],
  ![(437871476496467004127917433877903152600993/1071068069796696070145055000000000:ℝ), (1135860269753501153324035421042840815228757/267767017449174017536263750000000:ℝ), (622055841936030743571701560791032740799669/59503781655372003896947500000000:ℝ), (2609849043535968014208864478340869002024007/267767017449174017536263750000000:ℝ), (3351293757145043813841212231543006048899007/1071068069796696070145055000000000:ℝ)]]
theorem cell5_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highRegular cell5 4 b ν := by
 have heq : highRegular cell5 4 b ν = Record12518109.Bernstein.bsum 1 4 (432242142830470693690698376344361138600993/4679469562387855000000000000000000000000:ℝ) cell5_regular4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_regular4_g]
def cell5_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(45267163351395613428853396651342007/1793490940237268410140000000000:ℝ), (190765344966726169332111197666775979/2690236410355902615210000000000:ℝ), (249568311738002462972678527984348979/5380472820711805230420000000000:ℝ)],
  ![(134158938017368598035662179912026021/5380472820711805230420000000000:ℝ), (188915804621617037056993395666775979/2690236410355902615210000000000:ℝ), (27499323941733656122406350331594331/597830313412422803380000000000:ℝ)]]
theorem cell5_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 0 false b ν := by
 have heq : highBranch cell5 0 false b ν = Record12518109.Bernstein.bsum 1 2 (134158938017368598035662179912026021/355639686741476980000000000000000000:ℝ) cell5_exceptional0_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional0_0_g]
def cell5_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(5084062774581537830097656479534900520143/201676262738740595451832860000000000:ℝ), (7144679056095550351997128745261220270857/100838131369370297725916430000000000:ℝ), (1038799640823400057534621981242680233873/22408473637637843939092540000000000:ℝ)],
  ![(5022495821384989388811244624500614520143/201676262738740595451832860000000000:ℝ), (786150392561891417947116947703357807873/11204236818818921969546270000000000:ℝ), (9271442942941964186318434089559122104857/201676262738740595451832860000000000:ℝ)]]
theorem cell5_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 0 true b ν := by
 have heq : highBranch cell5 0 true b ν = Record12518109.Bernstein.bsum 1 2 (5022495821384989388811244624500614520143/13330442378130781641340000000000000000000:ℝ) cell5_exceptional0_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional0_1_g]
theorem cell5_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell5 0 b ν :=
 highExceptional_pos_of_branches (cell5_exceptional0_0 hb hν) (cell5_exceptional0_1 hb hν)
def cell5_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(360137666903388935442892504439053/94394260012487811060000000000:ℝ), (14165590482191903254132129364040841/141591390018731716590000000000:ℝ), (27452826482554532575357492930807841/283182780037463433180000000000:ℝ)],
  ![(1045503774013322443772861195317159/283182780037463433180000000000:ℝ), (14076309280275029000256521364040841/141591390018731716590000000000:ℝ), (9102744301647989554410455976935947/94394260012487811060000000000:ℝ)]]
theorem cell5_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 1 false b ν := by
 have heq : highBranch cell5 1 false b ν = Record12518109.Bernstein.bsum 1 2 (1045503774013322443772861195317159/18717878249551420000000000000000000:ℝ) cell5_exceptional1_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional1_0_g]
def cell5_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(40171621709853524277224181309990395797/10614540144144241865885940000000000:ℝ), (530664703344407180565245379853261593203/5307270072072120932942970000000000:ℝ), (342910514814057781475913365082994826401/3538180048048080621961980000000000:ℝ)],
  ![(38863162576076219298912847492396395797/10614540144144241865885940000000000:ℝ), (58590913115341407542879869561584621467/589696674674680103660330000000000:ℝ), (1023311783932327435003533944373984479203/10614540144144241865885940000000000:ℝ)]]
theorem cell5_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 1 true b ν := by
 have heq : highBranch cell5 1 true b ν = Record12518109.Bernstein.bsum 1 2 (38863162576076219298912847492396395797/701602230427935875860000000000000000000:ℝ) cell5_exceptional1_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional1_1_g]
theorem cell5_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell5 1 b ν :=
 highExceptional_pos_of_branches (cell5_exceptional1_0 hb hν) (cell5_exceptional1_1 hb hν)
def cell5_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(6212558259301926350616992202701909/141591390018731716590000000000:ℝ), (16536690488595565531476928162591/283182780037463433180000000:ℝ), (24450330191415385251800899003/1510308160199804976960000:ℝ)],
  ![(6163490778664572836884759043701909/141591390018731716590000000000:ℝ), (5459591949943750679179404054197/94394260012487811060000000:ℝ), (72360986440163568561384697009/4530924480599414930880000:ℝ)]]
theorem cell5_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 2 false b ν := by
 have heq : highBranch cell5 2 false b ν = Record12518109.Bernstein.bsum 1 2 (72360986440163568561384697009/299486051992822720000000000000:ℝ) cell5_exceptional2_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional2_0_g]
def cell5_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(232691885500136825472815427544239605047/5307270072072120932942970000000000:ℝ), (206397924947755307045637786401681701/3538180048048080621961980000000:ℝ), (2744549207307155026984339184243047/169832642306307869854175040000:ℝ)],
  ![(76950903609552386616424765553480868349/1769090024024040310980990000000000:ℝ), (613274744408694528400994189107045103/10614540144144241865885940000000:ℝ), (2707441531305031134295240770243047/169832642306307869854175040000:ℝ)]]
theorem cell5_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 2 true b ν := by
 have heq : highBranch cell5 2 true b ν = Record12518109.Bernstein.bsum 1 2 (2707441531305031134295240770243047/11225635686846974013760000000000000:ℝ) cell5_exceptional2_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional2_1_g]
theorem cell5_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell5 2 b ν :=
 highExceptional_pos_of_branches (cell5_exceptional2_0 hb hν) (cell5_exceptional2_1 hb hν)
def cell5_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(114686207614912189852568589954026021/5380472820711805230420000000000:ℝ), (165505586612477212602502797666775979/2690236410355902615210000000000:ℝ), (220379296381607672156670127984348979/5380472820711805230420000000000:ℝ)],
  ![(12560406175343771955741175545780669/597830313412422803380000000000:ℝ), (18184005140818675591931666185197331/298915156706211401690000000000:ℝ), (24256100013245346031738750331594331/597830313412422803380000000000:ℝ)]]
theorem cell5_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 3 false b ν := by
 have heq : highBranch cell5 3 false b ν = Record12518109.Bernstein.bsum 1 2 (113043655578093947601670579912026021/355639686741476980000000000000000000:ℝ) cell5_exceptional3_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional3_0_g]
def cell5_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(1430866214303402035960116445578300173381/67225420912913531817277620000000000:ℝ), (2065955844567745568967072362687073423619/33612710456456765908638810000000000:ℝ), (917233878311872730406128330442680233873/22408473637637843939092540000000000:ℝ)],
  ![(4231031689713657666593937481700614520143/201676262738740595451832860000000000:ℝ), (6128542010664709116428140872130220270857/100838131369370297725916430000000000:ℝ), (8177351080338218242161991232359122104857/201676262738740595451832860000000000:ℝ)]]
theorem cell5_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 3 true b ν := by
 have heq : highBranch cell5 3 true b ν = Record12518109.Bernstein.bsum 1 2 (4231031689713657666593937481700614520143/13330442378130781641340000000000000000000:ℝ) cell5_exceptional3_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional3_1_g]
theorem cell5_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell5 3 b ν :=
 highExceptional_pos_of_branches (cell5_exceptional3_0 hb hν) (cell5_exceptional3_1 hb hν)
def cell5_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(221778628137879256492277513317159/283182780037463433180000000000:ℝ), (12662496566627040385468529364040841/141591390018731716590000000000:ℝ), (8438866778399530975064630976935947/94394260012487811060000000000:ℝ)],
  ![(186869401441034893936461195317159/283182780037463433180000000000:ℝ), (4191071788236722043864307121346947/47197130006243905530000000000:ℝ), (25172006757588029013067767930807841/283182780037463433180000000000:ℝ)]]
theorem cell5_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 4 false b ν := by
 have heq : highBranch cell5 4 false b ν = Record12518109.Bernstein.bsum 1 2 (186869401441034893936461195317159/18717878249551420000000000000000000:ℝ) cell5_exceptional4_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional4_0_g]
def cell5_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(7987429522726470046706400109990395797/10614540144144241865885940000000000:ℝ), (52702692678587713962125295672584621467/589696674674680103660330000000000:ℝ), (948659379760830658520657876448984479203/10614540144144241865885940000000000:ℝ)],
  ![(2226323462983055022798355430798798599/3538180048048080621961980000000000:ℝ), (470977748800954912979801107254261593203/5307270072072120932942970000000000:ℝ), (943239619250984749096451725573984479203/10614540144144241865885940000000000:ℝ)]]
theorem cell5_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 4 true b ν := by
 have heq : highBranch cell5 4 true b ν = Record12518109.Bernstein.bsum 1 2 (6678970388949165068395066292396395797/701602230427935875860000000000000000000:ℝ) cell5_exceptional4_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional4_1_g]
theorem cell5_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell5 4 b ν :=
 highExceptional_pos_of_branches (cell5_exceptional4_0 hb hν) (cell5_exceptional4_1 hb hν)
def cell5_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(730232789356255994951673284146351/31464753337495937020000000000:ℝ), (296519652339139204278672530465272919/5642567521384776705810000000000:ℝ), (16448985478003890372366655874285086193/530401347010169010346140000000000:ℝ)],
  ![(6490532745463512744159243239317159/283182780037463433180000000000:ℝ), (13779425742279715162250745872867827193/265200673505084505173070000000000:ℝ), (5427943639200491160023187083095028731/176800449003389670115380000000000:ℝ)]]
theorem cell5_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 5 false b ν := by
 have heq : highBranch cell5 5 false b ν = Record12518109.Bernstein.bsum 1 2 (6490532745463512744159243239317159/18717878249551420000000000000000000:ℝ) cell5_exceptional5_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional5_0_g]
def cell5_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(246016341995199233004568489465242395797/10614540144144241865885940000000000:ℝ), (521809342483178192095055656982622585425219/9940516844991082507402182810000000000:ℝ), (205342576930605844683545536247323311849073/6627011229994055004934788540000000000:ℝ)],
  ![(242959183512943702328295605647648395797/10614540144144241865885940000000000:ℝ), (171974889391218852723283472447423528475073/3313505614997027502467394270000000000:ℝ), (609837318372629638137559187065594935547219/19881033689982165014804365620000000000:ℝ)]]
theorem cell5_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 5 true b ν := by
 have heq : highBranch cell5 5 true b ν = Record12518109.Bernstein.bsum 1 2 (242959183512943702328295605647648395797/701602230427935875860000000000000000000:ℝ) cell5_exceptional5_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional5_1_g]
theorem cell5_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell5 5 b ν :=
 highExceptional_pos_of_branches (cell5_exceptional5_0 hb hν) (cell5_exceptional5_1 hb hν)
def cell5_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(6212558259301926350616992202701909/141591390018731716590000000000:ℝ), (16536690488595565531476928162591/283182780037463433180000000:ℝ), (24450330191415385251800899003/1510308160199804976960000:ℝ)],
  ![(6163490778664572836884759043701909/141591390018731716590000000000:ℝ), (5459591949943750679179404054197/94394260012487811060000000:ℝ), (72360986440163568561384697009/4530924480599414930880000:ℝ)]]
theorem cell5_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 6 false b ν := by
 have heq : highBranch cell5 6 false b ν = Record12518109.Bernstein.bsum 1 2 (72360986440163568561384697009/299486051992822720000000000000:ℝ) cell5_exceptional6_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional6_0_g]
def cell5_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(232691885500136825472815427544239605047/5307270072072120932942970000000000:ℝ), (206397924947755307045637786401681701/3538180048048080621961980000000:ℝ), (2744549207307155026984339184243047/169832642306307869854175040000:ℝ)],
  ![(76950903609552386616424765553480868349/1769090024024040310980990000000000:ℝ), (613274744408694528400994189107045103/10614540144144241865885940000000:ℝ), (2707441531305031134295240770243047/169832642306307869854175040000:ℝ)]]
theorem cell5_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 6 true b ν := by
 have heq : highBranch cell5 6 true b ν = Record12518109.Bernstein.bsum 1 2 (2707441531305031134295240770243047/11225635686846974013760000000000000:ℝ) cell5_exceptional6_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional6_1_g]
theorem cell5_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell5 6 b ν :=
 highExceptional_pos_of_branches (cell5_exceptional6_0 hb hν) (cell5_exceptional6_1 hb hν)
def cell5_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(1828242753141499350776219852439053/94394260012487811060000000000:ℝ), (82622802676989916043857510155090973/1880855840461592235270000000000:ℝ), (4637468871104094649809344358095028731/176800449003389670115380000000000:ℝ)],
  ![(5403165900681706841922843239317159/283182780037463433180000000000:ℝ), (11492817259795750723337045872867827193/265200673505084505173070000000000:ℝ), (13747252052909867057130938449285086193/530401347010169010346140000000000:ℝ)]]
theorem cell5_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 7 false b ν := by
 have heq : highBranch cell5 7 false b ν = Record12518109.Bernstein.bsum 1 2 (5403165900681706841922843239317159/18717878249551420000000000000000000:ℝ) cell5_exceptional7_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional7_0_g]
def cell5_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(205258570552242802371041508265242395797/10614540144144241865885940000000000:ℝ), (436100396734231753031253439882622585425219/9940516844991082507402182810000000000:ℝ), (520949145206582050499628210329569935547219/19881033689982165014804365620000000000:ℝ)],
  ![(202201412069987271694768624447648395797/10614540144144241865885940000000000:ℝ), (430215722424710119106048200242270585425219/9940516844991082507402182810000000000:ℝ), (514758732787394154586550788653194935547219/19881033689982165014804365620000000000:ℝ)]]
theorem cell5_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highBranch cell5 7 true b ν := by
 have heq : highBranch cell5 7 true b ν = Record12518109.Bernstein.bsum 1 2 (202201412069987271694768624447648395797/701602230427935875860000000000000000000:ℝ) cell5_exceptional7_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_exceptional7_1_g]
theorem cell5_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell5 7 b ν :=
 highExceptional_pos_of_branches (cell5_exceptional7_0 hb hν) (cell5_exceptional7_1 hb hν)
def cell5_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(232819631152423355788365663/56128178434234870068800000000:ℝ)],
  ![(235600869839808088409565663/56128178434234870068800000000:ℝ)]]
theorem cell5_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 0 false b := by
 have heq : domainBranch cell5 0 false b = Record12518109.Bernstein.bsum 1 0 (232819631152423355788365663/56128178434234870068800000000000:ℝ) cell5_domain0_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain0_0_g]
def cell5_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(232819631152423355788365663/56128178434234870068800000000:ℝ)],
  ![(235600869839808088409565663/56128178434234870068800000000:ℝ)]]
theorem cell5_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 0 true b := by
 have heq : domainBranch cell5 0 true b = Record12518109.Bernstein.bsum 1 0 (232819631152423355788365663/56128178434234870068800000000000:ℝ) cell5_domain0_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain0_1_g]
def cell5_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(29986186081633575466630992419541/4679469562387855000000000000000:ℝ)],
  ![(30282799021780179607473904919541/4679469562387855000000000000000:ℝ)]]
theorem cell5_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 1 false b := by
 have heq : domainBranch cell5 1 false b = Record12518109.Bernstein.bsum 1 0 (29986186081633575466630992419541/4679469562387855000000000000000000:ℝ) cell5_domain1_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain1_0_g]
def cell5_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(110565102259305276417970288761593/9358939124775710000000000000000:ℝ)],
  ![(111158328139598484699656113761593/9358939124775710000000000000000:ℝ)]]
theorem cell5_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 1 true b := by
 have heq : domainBranch cell5 1 true b = Record12518109.Bernstein.bsum 1 0 (110565102259305276417970288761593/9358939124775710000000000000000000:ℝ) cell5_domain1_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain1_1_g]
def cell5_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(5299979623239285236380435282837/467946956238785500000000000000:ℝ)],
  ![(5188774589129567131957697782837/467946956238785500000000000000:ℝ)]]
theorem cell5_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 2 false b := by
 have heq : domainBranch cell5 2 false b = Record12518109.Bernstein.bsum 1 0 (5188774589129567131957697782837/467946956238785500000000000000000:ℝ) cell5_domain2_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain2_0_g]
def cell5_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(5783112094372073242578711860301/935893912477571000000000000000:ℝ)],
  ![(5560702026152637033733236860301/935893912477571000000000000000:ℝ)]]
theorem cell5_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 2 true b := by
 have heq : domainBranch cell5 2 true b = Record12518109.Bernstein.bsum 1 0 (5560702026152637033733236860301/935893912477571000000000000000000:ℝ) cell5_domain2_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain2_1_g]
def cell5_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(80115522101429019772961735721/9358939124775710000000000000:ℝ)],
  ![(121403410233238422974956735721/9358939124775710000000000000:ℝ)]]
theorem cell5_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 3 false b := by
 have heq : domainBranch cell5 3 false b = Record12518109.Bernstein.bsum 1 0 (80115522101429019772961735721/9358939124775710000000000000000:ℝ) cell5_domain3_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain3_0_g]
def cell5_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(80115522101429019772961735721/9358939124775710000000000000:ℝ)],
  ![(121403410233238422974956735721/9358939124775710000000000000:ℝ)]]
theorem cell5_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 3 true b := by
 have heq : domainBranch cell5 3 true b = Record12518109.Bernstein.bsum 1 0 (80115522101429019772961735721/9358939124775710000000000000000:ℝ) cell5_domain3_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain3_1_g]
def cell5_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(1075652024220685917968937/116986739059696375000000:ℝ)],
  ![(846585909428802867968937/116986739059696375000000:ℝ)]]
theorem cell5_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 4 false b := by
 have heq : domainBranch cell5 4 false b = Record12518109.Bernstein.bsum 1 0 (846585909428802867968937/116986739059696375000000000:ℝ) cell5_domain4_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain4_0_g]
def cell5_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(1075652024220685917968937/116986739059696375000000:ℝ)],
  ![(846585909428802867968937/116986739059696375000000:ℝ)]]
theorem cell5_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 4 true b := by
 have heq : domainBranch cell5 4 true b = Record12518109.Bernstein.bsum 1 0 (846585909428802867968937/116986739059696375000000000:ℝ) cell5_domain4_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain4_1_g]
def cell5_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(1310457235117100064271630550349/233973478119392750000000000000:ℝ)],
  ![(1326908201330695700357718050349/233973478119392750000000000000:ℝ)]]
theorem cell5_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 5 false b := by
 have heq : domainBranch cell5 5 false b = Record12518109.Bernstein.bsum 1 0 (1310457235117100064271630550349/233973478119392750000000000000000:ℝ) cell5_domain5_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain5_0_g]
def cell5_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(5145733839195386316108895900627/467946956238785500000000000000:ℝ)],
  ![(5178635771622577588281070900627/467946956238785500000000000000:ℝ)]]
theorem cell5_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 5 true b := by
 have heq : domainBranch cell5 5 true b = Record12518109.Bernstein.bsum 1 0 (5145733839195386316108895900627/467946956238785500000000000000000:ℝ) cell5_domain5_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain5_1_g]
def cell5_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(17959417080052968384812630205136449/237973371714582828757625000000000:ℝ)],
  ![(17321648698157515778660282823886449/237973371714582828757625000000000:ℝ)]]
theorem cell5_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 6 false b := by
 have heq : domainBranch cell5 6 false b = Record12518109.Bernstein.bsum 1 0 (17321648698157515778660282823886449/237973371714582828757625000000000000:ℝ) cell5_domain6_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain6_0_g]
def cell5_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(69841520194077367859353551502553229/951893486858331315030500000000000:ℝ)],
  ![(67290446666495557434744161977553229/951893486858331315030500000000000:ℝ)]]
theorem cell5_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 6 true b := by
 have heq : domainBranch cell5 6 true b = Record12518109.Bernstein.bsum 1 0 (67290446666495557434744161977553229/951893486858331315030500000000000000:ℝ) cell5_domain6_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain6_1_g]
def cell5_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(910617903470418853603981571/37435756499102840000000000:ℝ)],
  ![(1093199011133206700668381571/37435756499102840000000000:ℝ)]]
theorem cell5_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 7 false b := by
 have heq : domainBranch cell5 7 false b = Record12518109.Bernstein.bsum 1 0 (910617903470418853603981571/37435756499102840000000000000:ℝ) cell5_domain7_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain7_0_g]
def cell5_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(910617903470418853603981571/37435756499102840000000000:ℝ)],
  ![(1093199011133206700668381571/37435756499102840000000000:ℝ)]]
theorem cell5_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 7 true b := by
 have heq : domainBranch cell5 7 true b = Record12518109.Bernstein.bsum 1 0 (910617903470418853603981571/37435756499102840000000000000:ℝ) cell5_domain7_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain7_1_g]
def cell5_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(902529838219576880454357374157/23397347811939275000000000000:ℝ)],
  ![(869833380037570178339869874157/23397347811939275000000000000:ℝ)]]
theorem cell5_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 8 false b := by
 have heq : domainBranch cell5 8 false b = Record12518109.Bernstein.bsum 1 0 (869833380037570178339869874157/23397347811939275000000000000000:ℝ) cell5_domain8_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain8_0_g]
def cell5_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(1902264770326900319178475791161/46794695623878550000000000000:ℝ)],
  ![(1836871853962886914949500791161/46794695623878550000000000000:ℝ)]]
theorem cell5_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell5 8 true b := by
 have heq : domainBranch cell5 8 true b = Record12518109.Bernstein.bsum 1 0 (1836871853962886914949500791161/46794695623878550000000000000000:ℝ) cell5_domain8_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_domain8_1_g]
def cell5_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(5454583026578590401851/1497430259964113600000:ℝ)],
  ![(6472654647875848401851/1497430259964113600000:ℝ)]]
theorem cell5_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < ordinary cell5 0 b := by
 have heq : ordinary cell5 0 b = Record12518109.Bernstein.bsum 1 0 (5454583026578590401851/1497430259964113600000000:ℝ) cell5_ordinary0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordinary0_g]
def cell5_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(15111963551492387794447/4492290779892340800000:ℝ)],
  ![(12057748687600613794447/4492290779892340800000:ℝ)]]
theorem cell5_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < ordinary cell5 1 b := by
 have heq : ordinary cell5 1 b = Record12518109.Bernstein.bsum 1 0 (12057748687600613794447/4492290779892340800000000:ℝ) cell5_ordinary1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordinary1_g]
def cell5_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(2234394600190631976370901/4679469562387855000000:ℝ)],
  ![(2215305757291308388870901/4679469562387855000000:ℝ)]]
theorem cell5_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < ordinary cell5 2 b := by
 have heq : ordinary cell5 2 b = Record12518109.Bernstein.bsum 1 0 (2215305757291308388870901/4679469562387855000000000:ℝ) cell5_ordinary2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordinary2_g]
def cell5_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(389999989/20000000:ℝ)],
  ![(409999989/20000000:ℝ)]]
theorem cell5_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < ordinary cell5 3 b := by
 have heq : ordinary cell5 3 b = Record12518109.Bernstein.bsum 1 0 (389999989/20000000000:ℝ) cell5_ordinary3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordinary3_g]
def cell5_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(4138371864875890548445083/9358939124775710000000:ℝ)],
  ![(4081476300827691953445083/9358939124775710000000:ℝ)]]
theorem cell5_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < ordinary cell5 4 b := by
 have heq : ordinary cell5 4 b = Record12518109.Bernstein.bsum 1 0 (4081476300827691953445083/9358939124775710000000000:ℝ) cell5_ordinary4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordinary4_g]
def cell5_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(1507472487405125857/304990325012000000000000:ℝ)],
  ![(1507472487405125857/304990325012000000000000:ℝ)]]
theorem cell5_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < ordinary cell5 5 b := by
 have heq : ordinary cell5 5 b = Record12518109.Bernstein.bsum 1 0 (1507472487405125857/304990325012000000000000000:ℝ) cell5_ordinary5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordinary5_g]
def cell5_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(5454508155065592196171/1497430259964113600000:ℝ)],
  ![(6472579776362850196171/1497430259964113600000:ℝ)]]
theorem cell5_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 0 false b := by
 have heq : complementBranch cell5 0 false b = Record12518109.Bernstein.bsum 1 0 (5454508155065592196171/1497430259964113600000000:ℝ) cell5_complement0_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement0_0_g]
def cell5_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(4202136246624916320944478643/1194216562430529150400000000:ℝ)],
  ![(5014078920255715963317678643/1194216562430529150400000000:ℝ)]]
theorem cell5_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 0 true b := by
 have heq : complementBranch cell5 0 true b = Record12518109.Bernstein.bsum 1 0 (4202136246624916320944478643/1194216562430529150400000000000:ℝ) cell5_complement0_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement0_1_g]
def cell5_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(1691446705295968134439893429/37435756499102840000000000:ℝ)],
  ![(1665266166969213507581893429/37435756499102840000000000:ℝ)]]
theorem cell5_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 1 false b := by
 have heq : complementBranch cell5 1 false b = Record12518109.Bernstein.bsum 1 0 (1665266166969213507581893429/37435756499102840000000000000:ℝ) cell5_complement1_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement1_0_g]
def cell5_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(15806678031622607420843523244933/350801115213967937930000000000:ℝ)],
  ![(15561352546344436886073547244933/350801115213967937930000000000:ℝ)]]
theorem cell5_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 1 true b := by
 have heq : complementBranch cell5 1 true b = Record12518109.Bernstein.bsum 1 0 (15561352546344436886073547244933/350801115213967937930000000000000:ℝ) cell5_complement1_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement1_1_g]
def cell5_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(1196891983702971994254793429/37435756499102840000000000:ℝ)],
  ![(1068904283246491567396793429/37435756499102840000000000:ℝ)]]
theorem cell5_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 2 false b := by
 have heq : complementBranch cell5 2 false b = Record12518109.Bernstein.bsum 1 0 (1068904283246491567396793429/37435756499102840000000000000:ℝ) cell5_complement2_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement2_0_g]
def cell5_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(11172329374255038840203997419933/350801115213967937930000000000:ℝ)],
  ![(9972994424449740265084021419933/350801115213967937930000000000:ℝ)]]
theorem cell5_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 2 true b := by
 have heq : complementBranch cell5 2 true b = Record12518109.Bernstein.bsum 1 0 (9972994424449740265084021419933/350801115213967937930000000000000:ℝ) cell5_complement2_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement2_1_g]
def cell5_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(1440727820703188769486168429/37435756499102840000000000:ℝ)],
  ![(1439999072908865592628168429/37435756499102840000000000:ℝ)]]
theorem cell5_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 3 false b := by
 have heq : complementBranch cell5 3 false b = Record12518109.Bernstein.bsum 1 0 (1439999072908865592628168429/37435756499102840000000000000:ℝ) cell5_complement3_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement3_0_g]
def cell5_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(13457254043824820186703404701183/350801115213967937930000000000:ℝ)],
  ![(13450430924678431662020928701183/350801115213967937930000000000:ℝ)]]
theorem cell5_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 3 true b := by
 have heq : complementBranch cell5 3 true b = Record12518109.Bernstein.bsum 1 0 (13450430924678431662020928701183/350801115213967937930000000000000:ℝ) cell5_complement3_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement3_1_g]
def cell5_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(1378908480504064251963030929/37435756499102840000000000:ℝ)],
  ![(1365453837443525350105030929/37435756499102840000000000:ℝ)]]
theorem cell5_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 4 false b := by
 have heq : complementBranch cell5 4 false b = Record12518109.Bernstein.bsum 1 0 (1365453837443525350105030929/37435756499102840000000000000:ℝ) cell5_complement4_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement4_0_g]
def cell5_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(6438980230826937057061731986529/175400557606983968965000000000:ℝ)],
  ![(6375943079720797292198618986529/175400557606983968965000000000:ℝ)]]
theorem cell5_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 4 true b := by
 have heq : complementBranch cell5 4 true b = Record12518109.Bernstein.bsum 1 0 (6375943079720797292198618986529/175400557606983968965000000000000:ℝ) cell5_complement4_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement4_1_g]
def cell5_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(3953871/100000:ℝ)],
  ![(140163/4000:ℝ)]]
theorem cell5_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 5 false b := by
 have heq : complementBranch cell5 5 false b = Record12518109.Bernstein.bsum 1 0 (140163/4000000:ℝ) cell5_complement5_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement5_0_g]
def cell5_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(2212284380814732843544505951221/56128178434234870068800000000:ℝ)],
  ![(1959823006424244228947386703221/56128178434234870068800000000:ℝ)]]
theorem cell5_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 5 true b := by
 have heq : complementBranch cell5 5 true b = Record12518109.Bernstein.bsum 1 0 (1959823006424244228947386703221/56128178434234870068800000000000:ℝ) cell5_complement5_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement5_1_g]
def cell5_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(152559877112491471981363/1497430259964113600000:ℝ)],
  ![(145433375763410665981363/1497430259964113600000:ℝ)]]
theorem cell5_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 6 false b := by
 have heq : complementBranch cell5 6 false b = Record12518109.Bernstein.bsum 1 0 (145433375763410665981363/1497430259964113600000000:ℝ) cell5_complement6_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement6_0_g]
def cell5_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(5711450484682784088283972032221/56128178434234870068800000000:ℝ)],
  ![(5444328761694750698563512432221/56128178434234870068800000000:ℝ)]]
theorem cell5_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 6 true b := by
 have heq : complementBranch cell5 6 true b = Record12518109.Bernstein.bsum 1 0 (5444328761694750698563512432221/56128178434234870068800000000000:ℝ) cell5_complement6_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement6_1_g]
def cell5_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(214273301445415295671093429/224614538994617040000000000:ℝ)],
  ![(260681939631252328813093429/224614538994617040000000000:ℝ)]]
theorem cell5_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 7 false b := by
 have heq : complementBranch cell5 7 false b = Record12518109.Bernstein.bsum 1 0 (214273301445415295671093429/224614538994617040000000000000:ℝ) cell5_complement7_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement7_0_g]
def cell5_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(6988967320335622746936530482357/8419226765135230510320000000000:ℝ)],
  ![(8728641367389721496829176482357/8419226765135230510320000000000:ℝ)]]
theorem cell5_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 7 true b := by
 have heq : complementBranch cell5 7 true b = Record12518109.Bernstein.bsum 1 0 (6988967320335622746936530482357/8419226765135230510320000000000000:ℝ) cell5_complement7_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement7_1_g]
def cell5_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(3487023117392569536781693429/224614538994617040000000000:ℝ)],
  ![(4144274728356761369923693429/224614538994617040000000000:ℝ)]]
theorem cell5_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 8 false b := by
 have heq : complementBranch cell5 8 false b = Record12518109.Bernstein.bsum 1 0 (3487023117392569536781693429/224614538994617040000000000000:ℝ) cell5_complement8_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement8_0_g]
def cell5_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(129661448671482805166485150282357/8419226765135230510320000000000:ℝ)],
  ![(154297349867187976884777796282357/8419226765135230510320000000000:ℝ)]]
theorem cell5_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 8 true b := by
 have heq : complementBranch cell5 8 true b = Record12518109.Bernstein.bsum 1 0 (129661448671482805166485150282357/8419226765135230510320000000000000:ℝ) cell5_complement8_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement8_1_g]
def cell5_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(4305210571379358097059343429/224614538994617040000000000:ℝ)],
  ![(5115172925538138630201343429/224614538994617040000000000:ℝ)]]
theorem cell5_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 9 false b := by
 have heq : complementBranch cell5 9 false b = Record12518109.Bernstein.bsum 1 0 (4305210571379358097059343429/224614538994617040000000000000:ℝ) cell5_complement9_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement9_0_g]
def cell5_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(160329569009269600771372305232357/8419226765135230510320000000000:ℝ)],
  ![(190689526992137540731764951232357/8419226765135230510320000000000:ℝ)]]
theorem cell5_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 9 true b := by
 have heq : complementBranch cell5 9 true b = Record12518109.Bernstein.bsum 1 0 (160329569009269600771372305232357/8419226765135230510320000000000000:ℝ) cell5_complement9_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement9_1_g]
def cell5_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(5454508155065592196171/1497430259964113600000:ℝ)],
  ![(6472579776362850196171/1497430259964113600000:ℝ)]]
theorem cell5_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 10 false b := by
 have heq : complementBranch cell5 10 false b = Record12518109.Bernstein.bsum 1 0 (5454508155065592196171/1497430259964113600000000:ℝ) cell5_complement10_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement10_0_g]
def cell5_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(4202136246624916320944478643/1194216562430529150400000000:ℝ)],
  ![(5014078920255715963317678643/1194216562430529150400000000:ℝ)]]
theorem cell5_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 10 true b := by
 have heq : complementBranch cell5 10 true b = Record12518109.Bernstein.bsum 1 0 (4202136246624916320944478643/1194216562430529150400000000000:ℝ) cell5_complement10_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement10_1_g]
def cell5_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(16363711643979272102713/748715129982056800000:ℝ)],
  ![(19417926507871046102713/748715129982056800000:ℝ)]]
theorem cell5_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 11 false b := by
 have heq : complementBranch cell5 11 false b = Record12518109.Bernstein.bsum 1 0 (16363711643979272102713/748715129982056800000000:ℝ) cell5_complement11_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement11_0_g]
def cell5_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(1219771081517597587247295661221/56128178434234870068800000000:ℝ)],
  ![(1448734280083670778508836061221/56128178434234870068800000000:ℝ)]]
theorem cell5_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 11 true b := by
 have heq : complementBranch cell5 11 true b = Record12518109.Bernstein.bsum 1 0 (1219771081517597587247295661221/56128178434234870068800000000000:ℝ) cell5_complement11_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement11_1_g]
def cell5_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(38182006314537134607277/1497430259964113600000:ℝ)],
  ![(45308507663617940607277/1497430259964113600000:ℝ)]]
theorem cell5_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 12 false b := by
 have heq : complementBranch cell5 12 false b = Record12518109.Bernstein.bsum 1 0 (38182006314537134607277/1497430259964113600000000:ℝ) cell5_complement12_0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement12_0_g]
def cell5_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(1424225217102842891279876694221/56128178434234870068800000000:ℝ)],
  ![(1691348794250001204155417094221/56128178434234870068800000000:ℝ)]]
theorem cell5_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell5 12 true b := by
 have heq : complementBranch cell5 12 true b = Record12518109.Bernstein.bsum 1 0 (1424225217102842891279876694221/56128178434234870068800000000000:ℝ) cell5_complement12_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement12_1_g]
theorem cell5_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 0 b := complementReserve_pos_of_branches (cell5_complement0_0 hb hν) (cell5_complement0_1 hb hν)
theorem cell5_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 1 b := complementReserve_pos_of_branches (cell5_complement1_0 hb hν) (cell5_complement1_1 hb hν)
theorem cell5_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 2 b := complementReserve_pos_of_branches (cell5_complement2_0 hb hν) (cell5_complement2_1 hb hν)
theorem cell5_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 3 b := complementReserve_pos_of_branches (cell5_complement3_0 hb hν) (cell5_complement3_1 hb hν)
theorem cell5_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 4 b := complementReserve_pos_of_branches (cell5_complement4_0 hb hν) (cell5_complement4_1 hb hν)
theorem cell5_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 5 b := complementReserve_pos_of_branches (cell5_complement5_0 hb hν) (cell5_complement5_1 hb hν)
theorem cell5_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 6 b := complementReserve_pos_of_branches (cell5_complement6_0 hb hν) (cell5_complement6_1 hb hν)
theorem cell5_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 7 b := complementReserve_pos_of_branches (cell5_complement7_0 hb hν) (cell5_complement7_1 hb hν)
theorem cell5_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 8 b := complementReserve_pos_of_branches (cell5_complement8_0 hb hν) (cell5_complement8_1 hb hν)
theorem cell5_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 9 b := complementReserve_pos_of_branches (cell5_complement9_0 hb hν) (cell5_complement9_1 hb hν)
theorem cell5_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 10 b := complementReserve_pos_of_branches (cell5_complement10_0 hb hν) (cell5_complement10_1 hb hν)
theorem cell5_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 11 b := complementReserve_pos_of_branches (cell5_complement11_0 hb hν) (cell5_complement11_1 hb hν)
theorem cell5_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell5 12 b := complementReserve_pos_of_branches (cell5_complement12_0 hb hν) (cell5_complement12_1 hb hν)
theorem cell5_all_domains {b : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell5 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell5_domain0_0 (ν := (627/1000:ℝ)) hb (by norm_num)
   | true => exact cell5_domain0_1 (ν := (627/1000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell5_domain1_0 (ν := (627/1000:ℝ)) hb (by norm_num)
   | true => exact cell5_domain1_1 (ν := (627/1000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell5_domain2_0 (ν := (627/1000:ℝ)) hb (by norm_num)
   | true => exact cell5_domain2_1 (ν := (627/1000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell5_domain3_0 (ν := (627/1000:ℝ)) hb (by norm_num)
   | true => exact cell5_domain3_1 (ν := (627/1000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell5_domain4_0 (ν := (627/1000:ℝ)) hb (by norm_num)
   | true => exact cell5_domain4_1 (ν := (627/1000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell5_domain5_0 (ν := (627/1000:ℝ)) hb (by norm_num)
   | true => exact cell5_domain5_1 (ν := (627/1000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell5_domain6_0 (ν := (627/1000:ℝ)) hb (by norm_num)
   | true => exact cell5_domain6_1 (ν := (627/1000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell5_domain7_0 (ν := (627/1000:ℝ)) hb (by norm_num)
   | true => exact cell5_domain7_1 (ν := (627/1000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell5_domain8_0 (ν := (627/1000:ℝ)) hb (by norm_num)
   | true => exact cell5_domain8_1 (ν := (627/1000:ℝ)) hb (by norm_num)
end
end Record12518109Admission
