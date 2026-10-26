/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell7 : Cell := ⟨(9763743/10000000:ℝ), (906637/250000:ℝ), (1587/2500:ℝ), (9/250:ℝ), (3/80:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (513/100000:ℝ), (1/25:ℝ)⟩
def cell7_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(123364012664916944487054157963706392656973691/1374893069754059215110144000000000000:ℝ), (1226287551331747737393375313852701233832300059/343723267438514803777536000000000000:ℝ), (2291048170962822278835565001344788704487120059/229148844959009869185024000000000000:ℝ), (3281191081399348328966598973097916210349620059/343723267438514803777536000000000000:ℝ), (4170832579757373666393565335825731999412120059/1374893069754059215110144000000000000:ℝ)],
  ![(81994924629559409861313553641873896583973691/1374893069754059215110144000000000000:ℝ), (1161020314773534089211833910156654948207300059/343723267438514803777536000000000000:ℝ), (2204494840629253377927172103117010188862120059/229148844959009869185024000000000000:ℝ), (3176182448451803577133448107517593944724620059/343723267438514803777536000000000000:ℝ), (4050302875889911204477351750468065983787120059/1374893069754059215110144000000000000:ℝ)]]
theorem cell7_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highRegular cell7 2 b ν := by
 have heq : highRegular cell7 2 b ν = Record12518109.Bernstein.bsum 1 4 (81994924629559409861313553641873896583973691/5204364999418093261718750000000000000000000:ℝ) cell7_regular2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_regular2_g]
def cell7_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(83227215516289727302097170774560663952498691/1374893069754059215110144000000000000:ℝ), (1167713729652558216043419829245474400943025059/343723267438514803777536000000000000:ℝ), (2226819776129631294496340423388515412097845059/229148844959009869185024000000000000:ℝ), (3224965853070038710550969551630570730460345059/343723267438514803777536000000000000:ℝ), (4134919742225392650822770588241394332022845059/1374893069754059215110144000000000000:ℝ)],
  ![(23137328019793281832804973444534317879498691/1374893069754059215110144000000000000:ℝ), (1087125599171400987964069912545271865318025059/343723267438514803777536000000000000:ℝ), (2128182570811186197024394580688080646472845059/229148844959009869185024000000000000:ℝ), (3110836088669347021274258468765092214835345059/343723267438514803777536000000000000:ℝ), (4007898897706716633217798152786072066397845059/1374893069754059215110144000000000000:ℝ)]]
theorem cell7_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highRegular cell7 3 b ν := by
 have heq : highRegular cell7 3 b ν = Record12518109.Bernstein.bsum 1 4 (23137328019793281832804973444534317879498691/5204364999418093261718750000000000000000000:ℝ) cell7_regular3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_regular3_g]
def cell7_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(572711942111414674670295179873728316957698691/1374893069754059215110144000000000000:ℝ), (1338575082164393761313212595139068626437825059/343723267438514803777536000000000000:ℝ), (2131222594558633406110469199064854371592645059/229148844959009869185024000000000000:ℝ), (2933608645743320760164316583784988439955145059/343723267438514803777536000000000000:ℝ), (3731548635387250131121791209932530791517645059/1374893069754059215110144000000000000:ℝ)],
  ![(469434248414450427316801250312968170884698691/1374893069754059215110144000000000000:ℝ), (1222906045508392286226573359256241090812825059/343723267438514803777536000000000000:ℝ), (2005229693183167428672940988473794605967645059/229148844959009869185024000000000000:ℝ), (2799143625096624649534088850528884924330145059/343723267438514803777536000000000000:ℝ), (3590266665616205662694400561586583525892645059/1374893069754059215110144000000000000:ℝ)]]
theorem cell7_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highRegular cell7 4 b ν := by
 have heq : highRegular cell7 4 b ν = Record12518109.Bernstein.bsum 1 4 (469434248414450427316801250312968170884698691/5204364999418093261718750000000000000000000:ℝ) cell7_regular4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_regular4_g]
def cell7_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(25299098296508001028744461427448946907/1259788210133445461376000000000000:ℝ), (34569164411934295670754625730551306843/629894105066722730688000000000000:ℝ), (44448213867183385417658108887793146843/1259788210133445461376000000000000:ℝ)],
  ![(24601708211556316284347304249227946907/1259788210133445461376000000000000:ℝ), (33790002349731800888487933412426306843/629894105066722730688000000000000:ℝ), (43584592057876532689578553809668146843/1259788210133445461376000000000000:ℝ)]]
theorem cell7_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 0 false b ν := by
 have heq : highBranch cell7 0 false b ν = Record12518109.Bernstein.bsum 1 2 (24601708211556316284347304249227946907/63285078392924014062500000000000000000:ℝ) cell7_exceptional0_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional0_0_g]
def cell7_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(947179355064380346974369904577475788640081/47220641480431936228756608000000000000:ℝ), (1294714421920787972087081474134416212521169/23610320740215968114378304000000000000:ℝ), (1665076011303773426116509314301066767641169/47220641480431936228756608000000000000:ℝ)],
  ![(921141963793128716756703740453293045640081/47220641480431936228756608000000000000:ℝ), (1265608794507490014949278902253611837521169/23610320740215968114378304000000000000:ℝ), (1632801402071008605825130585479582392641169/47220641480431936228756608000000000000:ℝ)]]
theorem cell7_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 0 true b ν := by
 have heq : highBranch cell7 0 true b ν = Record12518109.Bernstein.bsum 1 2 (921141963793128716756703740453293045640081/2372114593401970819104687500000000000000000:ℝ) cell7_exceptional0_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional0_1_g]
theorem cell7_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell7 0 b ν :=
 highExceptional_pos_of_branches (cell7_exceptional0_0 hb hν) (cell7_exceptional0_1 hb hν)
def cell7_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(353524947323007522631802092079138653/66304642638602392704000000000000:ℝ), (2558308231272711522492118317387157597/33152321319301196352000000000000:ℝ), (4795143269949931054188925008702517597/66304642638602392704000000000000:ℝ)],
  ![(332238748963051855662862076120138653/66304642638602392704000000000000:ℝ), (2519077133318317085970294873012157597/33152321319301196352000000000000:ℝ), (4737825810829858484538253524327517597/66304642638602392704000000000000:ℝ)]]
theorem cell7_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 1 false b ν := by
 have heq : highBranch cell7 1 false b ν = Record12518109.Bernstein.bsum 1 2 (332238748963051855662862076120138653/3330793599627579687500000000000000000:ℝ) cell7_exceptional1_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional1_0_g]
def cell7_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(13192925790843603834699482917002717905399/2485296920022733485724032000000000000:ℝ), (95838248078492665337581851831473437583351/1242648460011366742862016000000000000:ℝ), (179684966288593191520291392883297322063351/2485296920022733485724032000000000000:ℝ)],
  ![(12400470022085404993732834740236520905399/2485296920022733485724032000000000000:ℝ), (94372996421459580504271178206990312583351/1242648460011366742862016000000000000:ℝ), (177541616339210455629718812275094197063351/2485296920022733485724032000000000000:ℝ)]]
theorem cell7_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 1 true b ν := by
 have heq : highBranch cell7 1 true b ν = Record12518109.Bernstein.bsum 1 2 (12400470022085404993732834740236520905399/124848136494840569426562500000000000000000:ℝ) cell7_exceptional1_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional1_1_g]
theorem cell7_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell7 1 b ν :=
 highExceptional_pos_of_branches (cell7_exceptional1_0 hb hν) (cell7_exceptional1_1 hb hν)
def cell7_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(717775099265050763087737299906799727/22101547546200797568000000000000:ℝ), (776864341445547703589806839001183/17681238036960638054400000000:ℝ), (237423382893320971917593235397/18859987239424680591360000:ℝ)],
  ![(704660773750981093667854061253799727/22101547546200797568000000000000:ℝ), (758605793194914209526001002001183/17681238036960638054400000000:ℝ), (229001695899978373961402235397/18859987239424680591360000:ℝ)]]
theorem cell7_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 2 false b ν := by
 have heq : highBranch cell7 2 false b ν = Record12518109.Bernstein.bsum 1 2 (2061015263099805365652620118573/8526831615046604000000000000000:ℝ) cell7_exceptional2_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional2_0_g]
def cell7_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(80651579089005237239419776795969840676423/2485296920022733485724032000000000000:ℝ), (87264686182589354452306094838844609207/1988237536018186788579225600000000:ℝ), (79954156476846991662484201895073319/6362360115258197723453521920000:ℝ)],
  ![(79182301103641636406853456934103643676423/2485296920022733485724032000000000000:ℝ), (85219926830500239607664127539671609207/1988237536018186788579225600000000:ℝ), (77126131383990103518124495538073319/6362360115258197723453521920000:ℝ)]]
theorem cell7_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 2 true b ν := by
 have heq : highBranch cell7 2 true b ν = Record12518109.Bernstein.bsum 1 2 (77126131383990103518124495538073319/319611229426791857732000000000000000:ℝ) cell7_exceptional2_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional2_1_g]
theorem cell7_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell7 2 b ν :=
 highExceptional_pos_of_branches (cell7_exceptional2_0 hb hν) (cell7_exceptional2_1 hb hν)
def cell7_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(7165000747059710872339338809149648969/419929403377815153792000000000000:ℝ), (10025537778766540953174940243517102281/209964701688907576896000000000000:ℝ), (13100267374504377806409434629264382281/419929403377815153792000000000000:ℝ)],
  ![(770281931712127698985957749971405441/46658822597535017088000000000000:ℝ), (1085090787929523262120671422682455809/23329411298767508544000000000000:ℝ), (158177696766280990498554521850486201/5184313621948335232000000000000:ℝ)]]
theorem cell7_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 3 false b ν := by
 have heq : highBranch cell7 3 false b ν = Record12518109.Bernstein.bsum 1 2 (20797612156227447872620859249227946907/63285078392924014062500000000000000000:ℝ) cell7_exceptional3_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional3_0_g]
def cell7_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(804590422622488372297627566642475788640081/47220641480431936228756608000000000000:ℝ), (1126320129952773531103754693319416212521169/23610320740215968114378304000000000000:ℝ), (1472135576915781370459364933486066767641169/47220641480431936228756608000000000000:ℝ)],
  ![(778553031351236742079961402518293045640081/47220641480431936228756608000000000000:ℝ), (1097214502539475573965952121438611837521169/23610320740215968114378304000000000000:ℝ), (1439860967683016550167986204664582392641169/47220641480431936228756608000000000000:ℝ)]]
theorem cell7_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 3 true b ν := by
 have heq : highBranch cell7 3 true b ν = Record12518109.Bernstein.bsum 1 2 (778553031351236742079961402518293045640081/2372114593401970819104687500000000000000000:ℝ) cell7_exceptional3_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional3_1_g]
theorem cell7_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell7 3 b ν :=
 highExceptional_pos_of_branches (cell7_exceptional3_0 hb hν) (cell7_exceptional3_1 hb hν)
def cell7_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(7165372684846329779056373780708839/2455727505133421952000000000000:ℝ), (763653560466885705196466105795719199/11050773773100398784000000000000:ℝ), (1474092059613891640928735002900839199/22101547546200797568000000000000:ℝ)],
  ![(57392954710298412355194025373379551/22101547546200797568000000000000:ℝ), (750576527815420893022524957670719199/11050773773100398784000000000000:ℝ), (484995413302400261459503724925279733/7367182515400265856000000000000:ℝ)]]
theorem cell7_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 4 false b ν := by
 have heq : highBranch cell7 4 false b ν = Record12518109.Bernstein.bsum 1 2 (172178864130895237065582076120138653/3330793599627579687500000000000000000:ℝ) cell7_exceptional4_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional4_0_g]
def cell7_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(7193401127679877299817636677002717905399/2485296920022733485724032000000000000:ℝ), (85817259866638450003647198071473437583351/1242648460011366742862016000000000000:ℝ), (165708789112582426946923239123297322063351/2485296920022733485724032000000000000:ℝ)],
  ![(6400945358921678458850988500236520905399/2485296920022733485724032000000000000:ℝ), (84352008209605365170336524446990312583351/1242648460011366742862016000000000000:ℝ), (163565439163199691056350658515094197063351/2485296920022733485724032000000000000:ℝ)]]
theorem cell7_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 4 true b ν := by
 have heq : highBranch cell7 4 true b ν = Record12518109.Bernstein.bsum 1 2 (6400945358921678458850988500236520905399/124848136494840569426562500000000000000000:ℝ) cell7_exceptional4_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional4_1_g]
theorem cell7_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell7 4 b ν :=
 highExceptional_pos_of_branches (cell7_exceptional4_0 hb hν) (cell7_exceptional4_1 hb hν)
def cell7_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(1256258177545143489849329166985388653/66304642638602392704000000000000:ℝ), (6541715984743471897325878256434636824811/154589274311901478589376000000000000:ℝ), (7574178700408964274290820650060183304811/309178548623802957178752000000000000:ℝ)],
  ![(1220740140758472779542451651026388653/66304642638602392704000000000000:ℝ), (6368670001879462114800343419614011824811/154589274311901478589376000000000000:ℝ), (7391464838522881120667219455919558304811/309178548623802957178752000000000000:ℝ)]]
theorem cell7_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 5 false b ν := by
 have heq : highBranch cell7 5 false b ν = Record12518109.Bernstein.bsum 1 2 (1220740140758472779542451651026388653/3330793599627579687500000000000000000:ℝ) cell7_exceptional5_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional5_0_g]
def cell7_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(47030075459259926293914050265713686655399/2485296920022733485724032000000000000:ℝ), (244947517607027556109931503213125883620015713/5794469769033003121965580608000000000000:ℝ), (283663313791671641973847306381142137562655713/11588939538066006243931161216000000000000:ℝ)],
  ![(45704167690753167483511490776447489655399/2485296920022733485724032000000000000:ℝ), (238485704532274957208719040389377971745015713/5794469769033003121965580608000000000000:ℝ), (276838339875705672106705683502403465687655713/11588939538066006243931161216000000000000:ℝ)]]
theorem cell7_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 5 true b ν := by
 have heq : highBranch cell7 5 true b ν = Record12518109.Bernstein.bsum 1 2 (45704167690753167483511490776447489655399/124848136494840569426562500000000000000000:ℝ) cell7_exceptional5_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional5_1_g]
theorem cell7_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell7 5 b ν :=
 highExceptional_pos_of_branches (cell7_exceptional5_0 hb hν) (cell7_exceptional5_1 hb hν)
def cell7_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(717775099265050763087737299906799727/22101547546200797568000000000000:ℝ), (776864341445547703589806839001183/17681238036960638054400000000:ℝ), (237423382893320971917593235397/18859987239424680591360000:ℝ)],
  ![(704660773750981093667854061253799727/22101547546200797568000000000000:ℝ), (758605793194914209526001002001183/17681238036960638054400000000:ℝ), (229001695899978373961402235397/18859987239424680591360000:ℝ)]]
theorem cell7_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 6 false b ν := by
 have heq : highBranch cell7 6 false b ν = Record12518109.Bernstein.bsum 1 2 (2061015263099805365652620118573/8526831615046604000000000000000:ℝ) cell7_exceptional6_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional6_0_g]
def cell7_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(80651579089005237239419776795969840676423/2485296920022733485724032000000000000:ℝ), (87264686182589354452306094838844609207/1988237536018186788579225600000000:ℝ), (79954156476846991662484201895073319/6362360115258197723453521920000:ℝ)],
  ![(79182301103641636406853456934103643676423/2485296920022733485724032000000000000:ℝ), (85219926830500239607664127539671609207/1988237536018186788579225600000000:ℝ), (77126131383990103518124495538073319/6362360115258197723453521920000:ℝ)]]
theorem cell7_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 6 true b ν := by
 have heq : highBranch cell7 6 true b ν = Record12518109.Bernstein.bsum 1 2 (77126131383990103518124495538073319/319611229426791857732000000000000000:ℝ) cell7_exceptional6_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional6_1_g]
theorem cell7_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell7 6 b ν :=
 highExceptional_pos_of_branches (cell7_exceptional6_0 hb hν) (cell7_exceptional6_1 hb hν)
def cell7_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(1059133221536331164489549166985388653/66304642638602392704000000000000:ℝ), (5519416209422794148876840756434636824811/154589274311901478589376000000000000:ℝ), (6448772819636700650545399790060183304811/309178548623802957178752000000000000:ℝ)],
  ![(1023615184749660454182671651026388653/66304642638602392704000000000000:ℝ), (5346370226558784366351305919614011824811/154589274311901478589376000000000000:ℝ), (6266058957750617496921798595919558304811/309178548623802957178752000000000000:ℝ)]]
theorem cell7_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 7 false b ν := by
 have heq : highBranch cell7 7 false b ν = Record12518109.Bernstein.bsum 1 2 (1023615184749660454182671651026388653/3330793599627579687500000000000000000:ℝ) cell7_exceptional7_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional7_0_g]
def cell7_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(39641240733181613902453416525713686655399/2485296920022733485724032000000000000:ℝ), (206628655128682592064816230600625883620015713/5794469769033003121965580608000000000000:ℝ), (241479725162684884564997696285762137562655713/11588939538066006243931161216000000000000:ℝ)],
  ![(38315332964674855092050857036447489655399/2485296920022733485724032000000000000:ℝ), (200166842053929993163603767776877971745015713/5794469769033003121965580608000000000000:ℝ), (234654751246718914697856073407023465687655713/11588939538066006243931161216000000000000:ℝ)]]
theorem cell7_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell7 7 true b ν := by
 have heq : highBranch cell7 7 true b ν = Record12518109.Bernstein.bsum 1 2 (38315332964674855092050857036447489655399/124848136494840569426562500000000000000000:ℝ) cell7_exceptional7_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_exceptional7_1_g]
theorem cell7_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell7 7 b ν :=
 highExceptional_pos_of_branches (cell7_exceptional7_0 hb hν) (cell7_exceptional7_1 hb hν)
def cell7_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(16864862834943018186457895731/5992710551752347332475000000000:ℝ)],
  ![(156212176616270679266374895731/5992710551752347332475000000000:ℝ)]]
theorem cell7_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 0 false b := by
 have heq : domainBranch cell7 0 false b = Record12518109.Bernstein.bsum 1 0 (16864862834943018186457895731/3995140367834898221650000000000000:ℝ) cell7_domain0_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain0_0_g]
def cell7_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(16864862834943018186457895731/5992710551752347332475000000000:ℝ)],
  ![(156212176616270679266374895731/5992710551752347332475000000000:ℝ)]]
theorem cell7_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 0 true b := by
 have heq : domainBranch cell7 0 true b = Record12518109.Bernstein.bsum 1 0 (16864862834943018186457895731/3995140367834898221650000000000000:ℝ) cell7_domain0_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain0_1_g]
def cell7_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(270260576140597940417526910835147/63951237112849530000000000000000:ℝ)],
  ![(210302999638105172362907596835147/63951237112849530000000000000000:ℝ)]]
theorem cell7_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 1 false b := by
 have heq : domainBranch cell7 1 false b = Record12518109.Bernstein.bsum 1 0 (210302999638105172362907596835147/42634158075233020000000000000000000:ℝ) cell7_domain1_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain1_0_g]
def cell7_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(163205233515212569674698136680243/21317079037616510000000000000000:ℝ)],
  ![(143219374681048313656491698680243/21317079037616510000000000000000:ℝ)]]
theorem cell7_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 1 true b := by
 have heq : domainBranch cell7 1 true b = Record12518109.Bernstein.bsum 1 0 (429658124043144940969475096040729/42634158075233020000000000000000000:ℝ) cell7_domain1_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain1_1_g]
def cell7_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(17527965972138747064506527732293/2131707903761651000000000000000:ℝ)],
  ![(19060350403966283395164561732293/2131707903761651000000000000000:ℝ)]]
theorem cell7_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 2 false b := by
 have heq : domainBranch cell7 2 false b = Record12518109.Bernstein.bsum 1 0 (52583897916416241193519583196879/4263415807523302000000000000000000:ℝ) cell7_domain2_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain2_0_g]
def cell7_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(31699472342135487159177951378053/6395123711284953000000000000000:ℝ)],
  ![(36296625637618096151152053378053/6395123711284953000000000000000:ℝ)]]
theorem cell7_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 2 true b := by
 have heq : domainBranch cell7 2 true b = Record12518109.Bernstein.bsum 1 0 (31699472342135487159177951378053/4263415807523302000000000000000000:ℝ) cell7_domain2_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain2_1_g]
def cell7_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(50096001530434530589899563681/21317079037616510000000000000:ℝ)],
  ![(167685914884222535122053563681/21317079037616510000000000000:ℝ)]]
theorem cell7_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 3 false b := by
 have heq : domainBranch cell7 3 false b = Record12518109.Bernstein.bsum 1 0 (150288004591303591769698691043/42634158075233020000000000000000:ℝ) cell7_domain3_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain3_0_g]
def cell7_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(50096001530434530589899563681/21317079037616510000000000000:ℝ)],
  ![(167685914884222535122053563681/21317079037616510000000000000:ℝ)]]
theorem cell7_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 3 true b := by
 have heq : domainBranch cell7 3 true b = Record12518109.Bernstein.bsum 1 0 (150288004591303591769698691043/42634158075233020000000000000000:ℝ) cell7_domain3_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain3_1_g]
def cell7_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(558697160687988746817321/66615871992551593750000:ℝ)],
  ![(394995208978829369817321/66615871992551593750000:ℝ)]]
theorem cell7_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 4 false b := by
 have heq : domainBranch cell7 4 false b = Record12518109.Bernstein.bsum 1 0 (1184985626936488109451963/133231743985103187500000000:ℝ) cell7_domain4_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain4_0_g]
def cell7_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(558697160687988746817321/66615871992551593750000:ℝ)],
  ![(394995208978829369817321/66615871992551593750000:ℝ)]]
theorem cell7_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 4 true b := by
 have heq : domainBranch cell7 4 true b = Record12518109.Bernstein.bsum 1 0 (1184985626936488109451963/133231743985103187500000000:ℝ) cell7_domain4_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain4_1_g]
def cell7_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(11759510469294809976010362810733/3197561855642476500000000000000:ℝ)],
  ![(8789422686074223894991116810733/3197561855642476500000000000000:ℝ)]]
theorem cell7_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 5 false b := by
 have heq : domainBranch cell7 5 false b = Record12518109.Bernstein.bsum 1 0 (8789422686074223894991116810733/2131707903761651000000000000000000:ℝ) cell7_domain5_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain5_0_g]
def cell7_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(7568793670768004842996148197477/1065853951880825500000000000000:ℝ)],
  ![(6578764409694476149323066197477/1065853951880825500000000000000:ℝ)]]
theorem cell7_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 5 true b := by
 have heq : domainBranch cell7 5 true b = Record12518109.Bernstein.bsum 1 0 (19736293229083428447969198592431/2131707903761651000000000000000000:ℝ) cell7_domain5_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain5_1_g]
def cell7_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(115874447867050458054684319684352087/2168150516230408304670500000000000:ℝ)],
  ![(111020035816556672481769607650352087/2168150516230408304670500000000000:ℝ)]]
theorem cell7_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 6 false b := by
 have heq : domainBranch cell7 6 false b = Record12518109.Bernstein.bsum 1 0 (333060107449670017445308822951056261/4336301032460816609341000000000000000:ℝ) cell7_domain6_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain6_0_g]
def cell7_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(112989545103959532089051620232152269/2168150516230408304670500000000000:ℝ)],
  ![(108135133053465746516136908198152269/2168150516230408304670500000000000:ℝ)]]
theorem cell7_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 6 true b := by
 have heq : domainBranch cell7 6 true b = Record12518109.Bernstein.bsum 1 0 (324405399160397239548410724594456807/4336301032460816609341000000000000000:ℝ) cell7_domain6_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain6_1_g]
def cell7_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(19228016536045431971684527687/1598780927821238250000000000:ℝ)],
  ![(28806311007377961687593527687/1598780927821238250000000000:ℝ)]]
theorem cell7_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 7 false b := by
 have heq : domainBranch cell7 7 false b = Record12518109.Bernstein.bsum 1 0 (19228016536045431971684527687/1065853951880825500000000000000:ℝ) cell7_domain7_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain7_0_g]
def cell7_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(19228016536045431971684527687/1598780927821238250000000000:ℝ)],
  ![(28806311007377961687593527687/1598780927821238250000000000:ℝ)]]
theorem cell7_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 7 true b := by
 have heq : domainBranch cell7 7 true b = Record12518109.Bernstein.bsum 1 0 (19228016536045431971684527687/1065853951880825500000000000000:ℝ) cell7_domain7_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain7_1_g]
def cell7_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(8737936627984398254609520097819/319756185564247650000000000000:ℝ)],
  ![(8177140560187007048589342097819/319756185564247650000000000000:ℝ)]]
theorem cell7_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 8 false b := by
 have heq : domainBranch cell7 8 false b = Record12518109.Bernstein.bsum 1 0 (8177140560187007048589342097819/213170790376165100000000000000000:ℝ) cell7_domain8_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain8_0_g]
def cell7_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(9159389184944157167685701066633/319756185564247650000000000000:ℝ)],
  ![(8598593117146765961665523066633/319756185564247650000000000000:ℝ)]]
theorem cell7_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell7 8 true b := by
 have heq : domainBranch cell7 8 true b = Record12518109.Bernstein.bsum 1 0 (8598593117146765961665523066633/213170790376165100000000000000000:ℝ) cell7_domain8_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_domain8_1_g]
def cell7_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(118895636961232861048847/63951237112849530000000:ℝ)],
  ![(173462954197619320048847/63951237112849530000000:ℝ)]]
theorem cell7_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell7 0 b := by
 have heq : ordinary cell7 0 b = Record12518109.Bernstein.bsum 1 0 (118895636961232861048847/42634158075233020000000000:ℝ) cell7_ordinary0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordinary0_g]
def cell7_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(577847226475541505353459/191853711338548590000000:ℝ)],
  ![(414145274766382128353459/191853711338548590000000:ℝ)]]
theorem cell7_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell7 1 b := by
 have heq : ordinary cell7 1 b = Record12518109.Bernstein.bsum 1 0 (414145274766382128353459/127902474225699060000000000:ℝ) cell7_ordinary1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordinary1_g]
def cell7_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(6886016849987863870215089/21317079037616510000000:ℝ)],
  ![(6776882215515090952215089/21317079037616510000000:ℝ)]]
theorem cell7_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell7 2 b := by
 have heq : ordinary cell7 2 b = Record12518109.Bernstein.bsum 1 0 (20330646646545272856645267/42634158075233020000000000:ℝ) cell7_ordinary2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordinary2_g]
def cell7_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(359999989/30000000:ℝ)],
  ![(389999989/30000000:ℝ)]]
theorem cell7_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell7 3 b := by
 have heq : ordinary cell7 3 b = Record12518109.Bernstein.bsum 1 0 (359999989/20000000000:ℝ) cell7_ordinary3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordinary3_g]
def cell7_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(19296528758728598999701589/63951237112849530000000:ℝ)],
  ![(18841222381084581185701589/63951237112849530000000:ℝ)]]
theorem cell7_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell7 4 b := by
 have heq : ordinary cell7 4 b = Record12518109.Bernstein.bsum 1 0 (18841222381084581185701589/42634158075233020000000000:ℝ) cell7_ordinary4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordinary4_g]
def cell7_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(3768611876220337217/1143713718795000000000000:ℝ)],
  ![(3768611876220337217/1143713718795000000000000:ℝ)]]
theorem cell7_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell7 5 b := by
 have heq : ordinary cell7 5 b = Record12518109.Bernstein.bsum 1 0 (3768611876220337217/762475812530000000000000000:ℝ) cell7_ordinary5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordinary5_g]
def cell7_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(39631168417776366465949/21317079037616510000000:ℝ)],
  ![(57820274163238519465949/21317079037616510000000:ℝ)]]
theorem cell7_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 0 false b := by
 have heq : complementBranch cell7 0 false b = Record12518109.Bernstein.bsum 1 0 (118893505253329099397847/42634158075233020000000000:ℝ) cell7_complement0_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement0_0_g]
def cell7_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(10664761009872659343193769801077/5992710551752347332475000000000:ℝ)],
  ![(15824576994395119336962908801077/5992710551752347332475000000000:ℝ)]]
theorem cell7_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 0 true b := by
 have heq : complementBranch cell7 0 true b = Record12518109.Bernstein.bsum 1 0 (10664761009872659343193769801077/3995140367834898221650000000000000:ℝ) cell7_complement0_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement0_1_g]
def cell7_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(16476960364631102045081215771/532926975940412750000000000:ℝ)],
  ![(15603080429250672147768215771/532926975940412750000000000:ℝ)]]
theorem cell7_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 1 false b := by
 have heq : complementBranch cell7 1 false b = Record12518109.Bernstein.bsum 1 0 (46809241287752016443304647313/1065853951880825500000000000000:ℝ) cell7_complement1_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement1_0_g]
def cell7_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(1847820949182897142045904657718949/59927105517523473324750000000000:ℝ)],
  ![(1750018515375240939393221510718949/59927105517523473324750000000000:ℝ)]]
theorem cell7_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 1 true b := by
 have heq : complementBranch cell7 1 true b = Record12518109.Bernstein.bsum 1 0 (1750018515375240939393221510718949/39951403678348982216500000000000000:ℝ) cell7_complement1_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement1_1_g]
def cell7_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(40269683259589342980358947313/1598780927821238250000000000:ℝ)],
  ![(32191311729809407388419947313/1598780927821238250000000000:ℝ)]]
theorem cell7_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 2 false b := by
 have heq : complementBranch cell7 2 false b = Record12518109.Bernstein.bsum 1 0 (32191311729809407388419947313/1065853951880825500000000000000:ℝ) cell7_complement2_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement2_0_g]
def cell7_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(1504431770759681691111361447618949/59927105517523473324750000000000:ℝ)],
  ![(1202094661754878124188978300618949/59927105517523473324750000000000:ℝ)]]
theorem cell7_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 2 true b := by
 have heq : complementBranch cell7 2 true b = Record12518109.Bernstein.bsum 1 0 (1202094661754878124188978300618949/39951403678348982216500000000000000:ℝ) cell7_complement2_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement2_1_g]
def cell7_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(41062641033661041923964822313/1598780927821238250000000000:ℝ)],
  ![(39805184158429413707025822313/1598780927821238250000000000:ℝ)]]
theorem cell7_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 3 false b := by
 have heq : complementBranch cell7 3 false b = Record12518109.Bernstein.bsum 1 0 (39805184158429413707025822313/1065853951880825500000000000000:ℝ) cell7_complement3_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement3_0_g]
def cell7_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(1534154207005211182614540460243949/59927105517523473324750000000000:ℝ)],
  ![(1487485441996841821029282313243949/59927105517523473324750000000000:ℝ)]]
theorem cell7_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 3 true b := by
 have heq : complementBranch cell7 3 true b = Record12518109.Bernstein.bsum 1 0 (1487485441996841821029282313243949/39951403678348982216500000000000000:ℝ) cell7_complement3_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement3_1_g]
def cell7_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(13305830434791015509868078271/532926975940412750000000000:ℝ)],
  ![(12659314321228862525055078271/532926975940412750000000000:ℝ)]]
theorem cell7_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 4 false b := by
 have heq : complementBranch cell7 4 false b = Record12518109.Bernstein.bsum 1 0 (37977942963686587575165234813/1065853951880825500000000000000:ℝ) cell7_complement4_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement4_0_g]
def cell7_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(1491230559702309251247722558981449/59927105517523473324750000000000:ℝ)],
  ![(1418994960294296469128751911981449/59927105517523473324750000000000:ℝ)]]
theorem cell7_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 4 true b := by
 have heq : complementBranch cell7 4 true b = Record12518109.Bernstein.bsum 1 0 (1418994960294296469128751911981449/39951403678348982216500000000000000:ℝ) cell7_complement4_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement4_1_g]
def cell7_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(790169/25000:ℝ)],
  ![(16943/625:ℝ)]]
theorem cell7_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 5 false b := by
 have heq : complementBranch cell7 5 false b = Record12518109.Bernstein.bsum 1 0 (50829/1250000:ℝ) cell7_complement5_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement5_0_g]
def cell7_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(188910487472753456392034233548577/5992710551752347332475000000000:ℝ)],
  ![(162001964223987244071481621548577/5992710551752347332475000000000:ℝ)]]
theorem cell7_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 5 true b := by
 have heq : complementBranch cell7 5 true b = Record12518109.Bernstein.bsum 1 0 (162001964223987244071481621548577/3995140367834898221650000000000000:ℝ) cell7_complement5_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement5_1_g]
def cell7_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(4687983779294946317507071/63951237112849530000000:ℝ)],
  ![(4306012558640241104507071/63951237112849530000000:ℝ)]]
theorem cell7_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 6 false b := by
 have heq : complementBranch cell7 6 false b = Record12518109.Bernstein.bsum 1 0 (4306012558640241104507071/42634158075233020000000000:ℝ) cell7_complement6_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement6_0_g]
def cell7_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(438799563312330616865650558281077/5992710551752347332475000000000:ℝ)],
  ![(403052444257423604005479697281077/5992710551752347332475000000000:ℝ)]]
theorem cell7_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 6 true b := by
 have heq : complementBranch cell7 6 true b = Record12518109.Bernstein.bsum 1 0 (403052444257423604005479697281077/3995140367834898221650000000000000:ℝ) cell7_complement6_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement6_1_g]
def cell7_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(1583374383696418930889515771/3197561855642476500000000000:ℝ)],
  ![(827357060538991669525505257/1065853951880825500000000000:ℝ)]]
theorem cell7_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 7 false b := by
 have heq : complementBranch cell7 7 false b = Record12518109.Bernstein.bsum 1 0 (1583374383696418930889515771/2131707903761651000000000000000:ℝ) cell7_complement7_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement7_0_g]
def cell7_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(16606859783673108671310720205311/39951403678348982216500000000000:ℝ)],
  ![(84435413519351047214406761615933/119854211035046946649500000000000:ℝ)]]
theorem cell7_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 7 true b := by
 have heq : complementBranch cell7 7 true b = Record12518109.Bernstein.bsum 1 0 (49820579351019326013932160615933/79902807356697964433000000000000000:ℝ) cell7_complement7_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement7_1_g]
def cell7_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(25362501775942991140658915771/3197561855642476500000000000:ℝ)],
  ![(37174662021140839018345915771/3197561855642476500000000000:ℝ)]]
theorem cell7_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 8 false b := by
 have heq : complementBranch cell7 8 false b = Record12518109.Bernstein.bsum 1 0 (25362501775942991140658915771/2131707903761651000000000000000:ℝ) cell7_complement8_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement8_0_g]
def cell7_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(941133611394597592152718580815933/119854211035046946649500000000000:ℝ)],
  ![(461605931985741347297531060605311/39951403678348982216500000000000:ℝ)]]
theorem cell7_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 8 true b := by
 have heq : complementBranch cell7 8 true b = Record12518109.Bernstein.bsum 1 0 (941133611394597592152718580815933/79902807356697964433000000000000000:ℝ) cell7_complement8_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement8_1_g]
def cell7_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(10435761208001544731033755257/1065853951880825500000000000:ℝ)],
  ![(45847809731021805020788265771/3197561855642476500000000000:ℝ)]]
theorem cell7_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 9 false b := by
 have heq : complementBranch cell7 9 false b = Record12518109.Bernstein.bsum 1 0 (31307283624004634193101265771/2131707903761651000000000000000:ℝ) cell7_complement9_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement9_0_g]
def cell7_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(1163961869405492158687415185865933/119854211035046946649500000000000:ℝ)],
  ![(1709913391566692290562139786865933/119854211035046946649500000000000:ℝ)]]
theorem cell7_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 9 true b := by
 have heq : complementBranch cell7 9 true b = Record12518109.Bernstein.bsum 1 0 (1163961869405492158687415185865933/79902807356697964433000000000000000:ℝ) cell7_complement9_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement9_1_g]
def cell7_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(39631168417776366465949/21317079037616510000000:ℝ)],
  ![(57820274163238519465949/21317079037616510000000:ℝ)]]
theorem cell7_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 10 false b := by
 have heq : complementBranch cell7 10 false b = Record12518109.Bernstein.bsum 1 0 (118893505253329099397847/42634158075233020000000000:ℝ) cell7_complement10_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement10_0_g]
def cell7_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(10664761009872659343193769801077/5992710551752347332475000000000:ℝ)],
  ![(15824576994395119336962908801077/5992710551752347332475000000000:ℝ)]]
theorem cell7_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 10 true b := by
 have heq : complementBranch cell7 10 true b = Record12518109.Bernstein.bsum 1 0 (10664761009872659343193769801077/3995140367834898221650000000000000:ℝ) cell7_complement10_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement10_1_g]
def cell7_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(356685845029746702321041/31975618556424765000000:ℝ)],
  ![(520387796738906079321041/31975618556424765000000:ℝ)]]
theorem cell7_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 11 false b := by
 have heq : complementBranch cell7 11 false b = Record12518109.Bernstein.bsum 1 0 (356685845029746702321041/21317079037616510000000000:ℝ) cell7_complement11_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement11_0_g]
def cell7_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(66371825512596300976867921063577/5992710551752347332475000000000:ℝ)],
  ![(97098475896762181504349560063577/5992710551752347332475000000000:ℝ)]]
theorem cell7_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 11 true b := by
 have heq : complementBranch cell7 11 true b = Record12518109.Bernstein.bsum 1 0 (66371825512596300976867921063577/3995140367834898221650000000000000:ℝ) cell7_complement11_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement11_1_g]
def cell7_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(277422442340242088563643/21317079037616510000000:ℝ)],
  ![(404746182558477159563643/21317079037616510000000:ℝ)]]
theorem cell7_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 12 false b := by
 have heq : complementBranch cell7 12 false b = Record12518109.Bernstein.bsum 1 0 (832267327020726265690929/42634158075233020000000000:ℝ) cell7_complement12_0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement12_0_g]
def cell7_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(77513238413141029303602751316077/5992710551752347332475000000000:ℝ)],
  ![(113353255677235593937826890316077/5992710551752347332475000000000:ℝ)]]
theorem cell7_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell7 12 true b := by
 have heq : complementBranch cell7 12 true b = Record12518109.Bernstein.bsum 1 0 (77513238413141029303602751316077/3995140367834898221650000000000000:ℝ) cell7_complement12_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement12_1_g]
theorem cell7_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 0 b := complementReserve_pos_of_branches (cell7_complement0_0 hb hν) (cell7_complement0_1 hb hν)
theorem cell7_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 1 b := complementReserve_pos_of_branches (cell7_complement1_0 hb hν) (cell7_complement1_1 hb hν)
theorem cell7_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 2 b := complementReserve_pos_of_branches (cell7_complement2_0 hb hν) (cell7_complement2_1 hb hν)
theorem cell7_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 3 b := complementReserve_pos_of_branches (cell7_complement3_0 hb hν) (cell7_complement3_1 hb hν)
theorem cell7_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 4 b := complementReserve_pos_of_branches (cell7_complement4_0 hb hν) (cell7_complement4_1 hb hν)
theorem cell7_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 5 b := complementReserve_pos_of_branches (cell7_complement5_0 hb hν) (cell7_complement5_1 hb hν)
theorem cell7_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 6 b := complementReserve_pos_of_branches (cell7_complement6_0 hb hν) (cell7_complement6_1 hb hν)
theorem cell7_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 7 b := complementReserve_pos_of_branches (cell7_complement7_0 hb hν) (cell7_complement7_1 hb hν)
theorem cell7_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 8 b := complementReserve_pos_of_branches (cell7_complement8_0 hb hν) (cell7_complement8_1 hb hν)
theorem cell7_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 9 b := complementReserve_pos_of_branches (cell7_complement9_0 hb hν) (cell7_complement9_1 hb hν)
theorem cell7_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 10 b := complementReserve_pos_of_branches (cell7_complement10_0 hb hν) (cell7_complement10_1 hb hν)
theorem cell7_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 11 b := complementReserve_pos_of_branches (cell7_complement11_0 hb hν) (cell7_complement11_1 hb hν)
theorem cell7_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell7 12 b := complementReserve_pos_of_branches (cell7_complement12_0 hb hν) (cell7_complement12_1 hb hν)
theorem cell7_all_domains {b : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell7 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell7_domain0_0 (ν := (1587/2500:ℝ)) hb (by norm_num)
   | true => exact cell7_domain0_1 (ν := (1587/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell7_domain1_0 (ν := (1587/2500:ℝ)) hb (by norm_num)
   | true => exact cell7_domain1_1 (ν := (1587/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell7_domain2_0 (ν := (1587/2500:ℝ)) hb (by norm_num)
   | true => exact cell7_domain2_1 (ν := (1587/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell7_domain3_0 (ν := (1587/2500:ℝ)) hb (by norm_num)
   | true => exact cell7_domain3_1 (ν := (1587/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell7_domain4_0 (ν := (1587/2500:ℝ)) hb (by norm_num)
   | true => exact cell7_domain4_1 (ν := (1587/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell7_domain5_0 (ν := (1587/2500:ℝ)) hb (by norm_num)
   | true => exact cell7_domain5_1 (ν := (1587/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell7_domain6_0 (ν := (1587/2500:ℝ)) hb (by norm_num)
   | true => exact cell7_domain6_1 (ν := (1587/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell7_domain7_0 (ν := (1587/2500:ℝ)) hb (by norm_num)
   | true => exact cell7_domain7_1 (ν := (1587/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell7_domain8_0 (ν := (1587/2500:ℝ)) hb (by norm_num)
   | true => exact cell7_domain8_1 (ν := (1587/2500:ℝ)) hb (by norm_num)
end
end Record12518109Admission
