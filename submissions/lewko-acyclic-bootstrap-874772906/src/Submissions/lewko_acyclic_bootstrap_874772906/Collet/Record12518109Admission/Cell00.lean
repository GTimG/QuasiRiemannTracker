/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell0 : Cell := ⟨(9958353/10000000:ℝ), (2129819/500000:ℝ), (357/500:ℝ), (39/2000:ℝ), (3/125:ℝ), (1/4:ℝ), (13/25:ℝ), (9981613/10000000:ℝ), (4380251/1000000:ℝ), (2/125:ℝ), (1/50:ℝ), (1/4:ℝ), (11/20:ℝ), (3/5000:ℝ), (1/25:ℝ)⟩
def cell0_regular0_g : Fin 2 → Fin 5 → ℝ := ![![(1091280432883436288808349581298103988043927/85878487778549381109000000000000:ℝ), (37313587214343646819152249601744129745458387/407922816948109560267750000000000:ℝ), (53502025612048508607035158081640731016009137/271948544632073040178500000000000:ℝ), (69255166240330180735204462189344415406852887/407922816948109560267750000000000:ℝ), (84533464690869471983432458103469165340446637/1631691267792438241071000000000000:ℝ)],
  ![(1654831008507195756489424308900558645043927/85878487778549381109000000000000:ℝ), (47320250548001284224189279410374311245458387/407922816948109560267750000000000:ℝ), (62825146296489078928442932095622184141009137/271948544632073040178500000000000:ℝ), (77912768573160605389710520913410821656852887/407922816948109560267750000000000:ℝ), (92544238724354696395984303792678149715446637/1631691267792438241071000000000000:ℝ)]]
theorem cell0_regular0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highRegular cell0 0 b ν := by
 have heq : highRegular cell0 0 b ν = Record12518109.Bernstein.bsum 1 4 (1091280432883436288808349581298103988043927/11362185401444851562500000000000000000000:ℝ) cell0_regular0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_regular0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_regular0_g]
def cell0_regular1_g : Fin 2 → Fin 5 → ℝ := ![![(1282400279326528549709890523890638006793927/85878487778549381109000000000000:ℝ), (2391146160754599035764683581313663524103073/21469621944637345277250000000000:ℝ), (3465928887874597140126160096634971889987323/14313081296424896851500000000000:ℝ), (4504764172089201497792176431478702688518573/21469621944637345277250000000000:ℝ), (5505927344235327738264546919764961114299823/85878487778549381109000000000000:ℝ)],
  ![(1934160019823001438319100200430592663793927/85878487778549381109000000000000:ℝ), (3060518736030543113553696361621502024103073/21469621944637345277250000000000:ℝ), (4150731611041883071665459520068206264987323/14313081296424896851500000000000:ℝ), (5202937143915574315283365814365421438518573/21469621944637345277250000000000:ℝ), (6215528001093239893580694379970039239299823/85878487778549381109000000000000:ℝ)]]
theorem cell0_regular1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highRegular cell0 1 b ν := by
 have heq : highRegular cell0 1 b ν = Record12518109.Bernstein.bsum 1 4 (1282400279326528549709890523890638006793927/11362185401444851562500000000000000000000:ℝ) cell0_regular1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_regular1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_regular1_g]
def cell0_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(11062273667702136295787229353948034343927/85878487778549381109000000000000:ℝ), (848971521761201446495911622904395590303073/21469621944637345277250000000000:ℝ), (1668909989207188894421223662128558737437323/14313081296424896851500000000000:ℝ), (2468578004758055733522871748184240317218573/21469621944637345277250000000000:ℝ), (3245924423848546577102852789423721399249823/85878487778549381109000000000000:ℝ)],
  ![(76050593837098097699276414759402691343927/85878487778549381109000000000000:ℝ), (869071911645637219529433435555984090303073/21469621944637345277250000000000:ℝ), (1645630309894541559603483507436793112437323/14313081296424896851500000000000:ℝ), (2403476124376366385452844822477209067218573/21469621944637345277250000000000:ℝ), (3140600205648889673500177007441299524249823/85878487778549381109000000000000:ℝ)]]
theorem cell0_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highRegular cell0 2 b ν := by
 have heq : highRegular cell0 2 b ν = Record12518109.Bernstein.bsum 1 4 (11062273667702136295787229353948034343927/11362185401444851562500000000000000000000:ℝ) cell0_regular2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_regular2_g]
def cell0_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(671033070122088999515724687043702993927/85878487778549381109000000000000:ℝ), (824516247287182110295796314669239196653073/21469621944637345277250000000000:ℝ), (1633617944507166801021759891785686506287323/14313081296424896851500000000000:ℝ), (2425684051006625630355222111048800898568573/21469621944637345277250000000000:ℝ), (3198616249572476767056778779271289793099823/85878487778549381109000000000000:ℝ)],
  ![(691147850572216909856733776498359993927/85878487778549381109000000000000:ℝ), (785584968297522693903749684945827696653073/21469621944637345277250000000000:ℝ), (1557061676044260962916904018343920881287323/14313081296424896851500000000000:ℝ), (2312864295547602034564786982216769648568573/21469621944637345277250000000000:ℝ), (3050924820420406882571290497288867918099823/85878487778549381109000000000000:ℝ)]]
theorem cell0_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highRegular cell0 3 b ν := by
 have heq : highRegular cell0 3 b ν = Record12518109.Bernstein.bsum 1 4 (671033070122088999515724687043702993927/11362185401444851562500000000000000000000:ℝ) cell0_regular3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_regular3_g]
def cell0_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(551170408850235644890517086302861546193927/85878487778549381109000000000000:ℝ), (1208100220205659490097882054843851646453073/21469621944637345277250000000000:ℝ), (1867130377277306017215781418794935881087323/14313081296424896851500000000000:ℝ), (2527077278805112492155190686973090898368573/21469621944637345277250000000000:ℝ), (3186825955622636534341832256795970417899823/85878487778549381109000000000000:ℝ)],
  ![(406475035649474971437648597601816203193927/85878487778549381109000000000000:ℝ), (1038286280384020600405215521120440146453073/21469621944637345277250000000000:ℝ), (1673042793933110752331549834415670256087323/14313081296424896851500000000000:ℝ), (2309544260522681337350347355016059648368573/21469621944637345277250000000000:ℝ), (2946659131114627752517354717001048542899823/85878487778549381109000000000000:ℝ)]]
theorem cell0_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highRegular cell0 4 b ν := by
 have heq : highRegular cell0 4 b ν = Record12518109.Bernstein.bsum 1 4 (406475035649474971437648597601816203193927/11362185401444851562500000000000000000000:ℝ) cell0_regular4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_regular4_g]
def cell0_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(89495995078722781637922865830229121/1060228244179621989000000000000:ℝ), (1862842145492499427667490346302724451/10072168319706408895500000000000:ℝ), (2028986048786541193530932883106615451/20144336639412817791000000000000:ℝ)],
  ![(84469237890237052477336578741229121/1060228244179621989000000000000:ℝ), (1763822000873263288962481121427724451/10072168319706408895500000000000:ℝ), (1926379968058346567889031148731615451/20144336639412817791000000000000:ℝ)]]
theorem cell0_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highBranch cell0 0 false b ν := by
 have heq : highBranch cell0 0 false b ν = Record12518109.Bernstein.bsum 1 2 (84469237890237052477336578741229121/181794966423117625000000000000000000:ℝ) cell0_exceptional0_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_exceptional0_0_g]
def cell0_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(3354266509776586455482821907849058317443/39740535276584771013687000000000000:ℝ), (69819095143907244712961976932027417471833/377535085127555324630026500000000000:ℝ), (76046775676914112692900206389853037374833/755070170255110649260053000000000000:ℝ)],
  ![(3165905153787143662914536298817071317443/39740535276584771013687000000000000:ℝ), (66108587318391351196206491643137792471833/377535085127555324630026500000000000:ℝ), (72201845373048274803012121045899912374833/755070170255110649260053000000000000:ℝ)]]
theorem cell0_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highBranch cell0 0 true b ν := by
 have heq : highBranch cell0 0 true b ν = Record12518109.Bernstein.bsum 1 2 (3165905153787143662914536298817071317443/6814220726437717937875000000000000000000:ℝ) cell0_exceptional0_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_exceptional0_1_g]
theorem cell0_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
 (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell0 0 b ν :=
 highExceptional_pos_of_branches (cell0_exceptional0_0 hb hν) (cell0_exceptional0_1 hb hν)
def cell0_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(101536556886777993571019688686479121/1060228244179621989000000000000:ℝ), (140178748940662805542541729451788129/530114122089810994500000000000:ℝ), (179017028589141048530720961863177129/1060228244179621989000000000000:ℝ)],
  ![(95993411597270851453449026597479121/1060228244179621989000000000000:ℝ), (133791309500784921430366901826788129/530114122089810994500000000000:ℝ), (171781390889894990724835508738177129/1060228244179621989000000000000:ℝ)]]
theorem cell0_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highBranch cell0 1 false b ν := by
 have heq : highBranch cell0 1 false b ν = Record12518109.Bernstein.bsum 1 2 (95993411597270851453449026597479121/181794966423117625000000000000000000:ℝ) cell0_exceptional1_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_exceptional1_0_g]
def cell0_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(3805582888027919964371090118969877067443/39740535276584771013687000000000000:ℝ), (5254013888880331764661693554597290064307/19870267638292385506843500000000000:ℝ), (6709794841040889139749658504694719401307/39740535276584771013687000000000000:ℝ)],
  ![(3597865756847891549936159181812890067443/39740535276584771013687000000000000:ℝ), (5014649509789438227660011621629415064307/19870267638292385506843500000000000:ℝ), (6438636876321579747803618137085344401307/39740535276584771013687000000000000:ℝ)]]
theorem cell0_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highBranch cell0 1 true b ν := by
 have heq : highBranch cell0 1 true b ν = Record12518109.Bernstein.bsum 1 2 (3597865756847891549936159181812890067443/6814220726437717937875000000000000000000:ℝ) cell0_exceptional1_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_exceptional1_1_g]
theorem cell0_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
 (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell0 1 b ν :=
 highExceptional_pos_of_branches (cell0_exceptional1_0 hb hν) (cell0_exceptional1_1 hb hν)
def cell0_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(7126761323334423066940278512770013/117803138242180221000000000000:ℝ), (139840270439305072162678428517171/1413637658906162652000000000:ℝ), (878281828587517082256002910247/22618202542498602432000000:ℝ)],
  ![(6742576859687515771414399391770013/117803138242180221000000000000:ℝ), (131310245363150617968337221517171/1413637658906162652000000000:ℝ), (815372153679168568563779910247/22618202542498602432000000:ℝ)]]
theorem cell0_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highBranch cell0 2 false b ν := by
 have heq : highBranch cell0 2 false b ν = Record12518109.Bernstein.bsum 1 2 (2446116461037505705691339730741/11634877851079528000000000000000:ℝ) cell0_exceptional2_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_exceptional2_0_g]
def cell0_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(2403874532559589256932621540785670300511/39740535276584771013687000000000000:ℝ), (15722408142736128313473524104004003179/158962141106339084054748000000000:ℝ), (98742355749876839575795989243543503/2543394257701425344875968000000:ℝ)],
  ![(2274327640008263815066822986878683300511/39740535276584771013687000000000000:ℝ), (14763663460420029639173786765261003179/158962141106339084054748000000000:ℝ), (91671774078445915498304905716543503/2543394257701425344875968000000:ℝ)]]
theorem cell0_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highBranch cell0 2 true b ν := by
 have heq : highBranch cell0 2 true b ν = Record12518109.Bernstein.bsum 1 2 (91671774078445915498304905716543503/436110126492013948024000000000000000:ℝ) cell0_exceptional2_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_exceptional2_1_g]
theorem cell0_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
 (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell0 2 b ν :=
 highExceptional_pos_of_branches (cell0_exceptional2_0 hb hν) (cell0_exceptional2_1 hb hν)
def cell0_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(25743788306785420111837621943409707/353409414726540663000000000000:ℝ), (539488542992123687368593448767574817/3357389439902136298500000000000:ℝ), (591146683177792160363074294368871817/6714778879804272597000000000000:ℝ)],
  ![(24068202577290177058308859580409707/353409414726540663000000000000:ℝ), (506481828119044974466923707142574817/3357389439902136298500000000000:ℝ), (556944656268393951815773716243871817/6714778879804272597000000000000:ℝ)]]
theorem cell0_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highBranch cell0 3 false b ν := by
 have heq : highBranch cell0 3 false b ν = Record12518109.Bernstein.bsum 1 2 (72204607731870531174926578741229121/181794966423117625000000000000000000:ℝ) cell0_exceptional3_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_exceptional3_0_g]
def cell0_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(2894551377550534137504587877849058317443/39740535276584771013687000000000000:ℝ), (60659130175333205186612401002027417471833/377535085127555324630026500000000000:ℝ), (66468144986907739776447590459853037374833/755070170255110649260053000000000000:ℝ)],
  ![(2706190021561091344936302268817071317443/39740535276584771013687000000000000:ℝ), (56948622349817311669856915713137792471833/377535085127555324630026500000000000:ℝ), (62623214683041901886559505115899912374833/755070170255110649260053000000000000:ℝ)]]
theorem cell0_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highBranch cell0 3 true b ν := by
 have heq : highBranch cell0 3 true b ν = Record12518109.Bernstein.bsum 1 2 (2706190021561091344936302268817071317443/6814220726437717937875000000000000000000:ℝ) cell0_exceptional3_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_exceptional3_1_g]
theorem cell0_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
 (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell0 3 b ν :=
 highExceptional_pos_of_branches (cell0_exceptional3_0 hb hν) (cell0_exceptional3_1 hb hν)
def cell0_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(29599147288682378422453229562159707/353409414726540663000000000000:ℝ), (41876813167094569444567243150596043/176704707363270331500000000000:ℝ), (18074327664685898537153440207019681/117803138242180221000000000000:ℝ)],
  ![(27751432192179997716596342199159707/353409414726540663000000000000:ℝ), (39747666687135274740508967275596043/176704707363270331500000000000:ℝ), (5756789306775075149203537360673227/39267712747393407000000000000:ℝ)]]
theorem cell0_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highBranch cell0 4 false b ν := by
 have heq : highBranch cell0 4 false b ν = Record12518109.Bernstein.bsum 1 2 (83254296576539993149789026597479121/181794966423117625000000000000000000:ℝ) cell0_exceptional4_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_exceptional4_0_g]
def cell0_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(3328082639705865202575002338969877067443/39740535276584771013687000000000000:ℝ), (4708699606164085063982743834597290064307/19870267638292385506843500000000000:ℝ), (6097019773132909031485746284694719401307/39740535276584771013687000000000000:ℝ)],
  ![(3120365508525836788140071401812890067443/39740535276584771013687000000000000:ℝ), (4469335227073191526981061901629415064307/19870267638292385506843500000000000:ℝ), (5825861808413599639539705917085344401307/39740535276584771013687000000000000:ℝ)]]
theorem cell0_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highBranch cell0 4 true b ν := by
 have heq : highBranch cell0 4 true b ν = Record12518109.Bernstein.bsum 1 2 (3120365508525836788140071401812890067443/6814220726437717937875000000000000000000:ℝ) cell0_exceptional4_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_exceptional4_1_g]
theorem cell0_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
 (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell0 4 b ν :=
 highExceptional_pos_of_branches (cell0_exceptional4_0 hb hν) (cell0_exceptional4_1 hb hν)
def cell0_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(13807880051240163240438891097/4906238923035156915270000000000:ℝ)],
  ![(21411513632578603281225891097/4906238923035156915270000000000:ℝ)]]
theorem cell0_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 0 false b := by
 have heq : domainBranch cell0 0 false b = Record12518109.Bernstein.bsum 1 0 (13807880051240163240438891097/1090275316230034870060000000000000:ℝ) cell0_domain0_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain0_0_g]
def cell0_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(13807880051240163240438891097/4906238923035156915270000000000:ℝ)],
  ![(21411513632578603281225891097/4906238923035156915270000000000:ℝ)]]
theorem cell0_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 0 true b := by
 have heq : domainBranch cell0 0 true b = Record12518109.Bernstein.bsum 1 0 (13807880051240163240438891097/1090275316230034870060000000000000:ℝ) cell0_domain0_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain0_1_g]
def cell0_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(171726606767230650914662551677/161995514634461250000000000000:ℝ)],
  ![(134561138838558563344245051677/161995514634461250000000000000:ℝ)]]
theorem cell0_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 1 false b := by
 have heq : domainBranch cell0 1 false b = Record12518109.Bernstein.bsum 1 0 (134561138838558563344245051677/35999003252102500000000000000000:ℝ) cell0_domain1_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain1_0_g]
def cell0_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(97139131847268162430997425319/80997757317230625000000000000:ℝ)],
  ![(78556397882932118645788675319/80997757317230625000000000000:ℝ)]]
theorem cell0_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 1 true b := by
 have heq : domainBranch cell0 1 true b = Record12518109.Bernstein.bsum 1 0 (78556397882932118645788675319/17999501626051250000000000000000:ℝ) cell0_domain1_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain1_1_g]
def cell0_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(502023294457282654541849190397/545384899269352875000000000000:ℝ)],
  ![(580926663643206240780006690397/545384899269352875000000000000:ℝ)]]
theorem cell0_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 2 false b := by
 have heq : domainBranch cell0 2 false b = Record12518109.Bernstein.bsum 1 0 (1506069883371847963625547571191/363589932846235250000000000000000:ℝ) cell0_domain2_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain2_0_g]
def cell0_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(13360398020769206161390439549/17043278102167277343750000000:ℝ)],
  ![(989133019239332389458303839/1065204881385454833984375000:ℝ)]]
theorem cell0_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 2 true b := by
 have heq : domainBranch cell0 2 true b = Record12518109.Bernstein.bsum 1 0 (40081194062307618484171318647/11362185401444851562500000000000:ℝ) cell0_domain2_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain2_1_g]
def cell0_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(122174027463424777667422126193/327230939561611725000000000000:ℝ)],
  ![(1741530817742485575200035876193/327230939561611725000000000000:ℝ)]]
theorem cell0_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 3 false b := by
 have heq : domainBranch cell0 3 false b = Record12518109.Bernstein.bsum 1 0 (122174027463424777667422126193/72717986569247050000000000000000:ℝ) cell0_domain3_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain3_0_g]
def cell0_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(122174027463424777667422126193/327230939561611725000000000000:ℝ)],
  ![(1741530817742485575200035876193/327230939561611725000000000000:ℝ)]]
theorem cell0_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 3 true b := by
 have heq : domainBranch cell0 3 true b = Record12518109.Bernstein.bsum 1 0 (122174027463424777667422126193/72717986569247050000000000000000:ℝ) cell0_domain3_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain3_1_g]
def cell0_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(5518359110599407517041407/1308923758246446900000000:ℝ)],
  ![(2036201801029726274541407/1308923758246446900000000:ℝ)]]
theorem cell0_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 4 false b := by
 have heq : domainBranch cell0 4 false b = Record12518109.Bernstein.bsum 1 0 (2036201801029726274541407/290871946276988200000000000:ℝ) cell0_domain4_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain4_0_g]
def cell0_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(5518359110599407517041407/1308923758246446900000000:ℝ)],
  ![(2036201801029726274541407/1308923758246446900000000:ℝ)]]
theorem cell0_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 4 true b := by
 have heq : domainBranch cell0 4 true b = Record12518109.Bernstein.bsum 1 0 (2036201801029726274541407/290871946276988200000000000:ℝ) cell0_domain4_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain4_1_g]
def cell0_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(863102727409565469267513951221/818077348904029312500000000000:ℝ)],
  ![(675593770541281005274848951221/818077348904029312500000000000:ℝ)]]
theorem cell0_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 5 false b := by
 have heq : domainBranch cell0 5 false b = Record12518109.Bernstein.bsum 1 0 (675593770541281005274848951221/181794966423117625000000000000000:ℝ) cell0_domain5_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain5_0_g]
def cell0_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(108553679617208094058972067461/90897483211558812500000000000:ℝ)],
  ![(87719351076287598059787067461/90897483211558812500000000000:ℝ)]]
theorem cell0_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 5 true b := by
 have heq : domainBranch cell0 5 true b = Record12518109.Bernstein.bsum 1 0 (789474159686588382538083607149/181794966423117625000000000000000:ℝ) cell0_domain5_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain5_1_g]
def cell0_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(1253485398528729892670247899792996831/71667682512284466002148750000000000:ℝ)],
  ![(1035327535487547585439567206640496831/71667682512284466002148750000000000:ℝ)]]
theorem cell0_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 6 false b := by
 have heq : domainBranch cell0 6 false b = Record12518109.Bernstein.bsum 1 0 (1035327535487547585439567206640496831/15926151669396548000477500000000000000:ℝ) cell0_domain6_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain6_0_g]
def cell0_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(625264636137490371201772208711214157/35833841256142233001074375000000000:ℝ)],
  ![(516185704616899217586431862134964157/35833841256142233001074375000000000:ℝ)]]
theorem cell0_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 6 true b := by
 have heq : domainBranch cell0 6 true b = Record12518109.Bernstein.bsum 1 0 (516185704616899217586431862134964157/7963075834698274000238750000000000000:ℝ) cell0_domain6_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain6_1_g]
def cell0_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(4803731500949793904807405679/6544618791232234500000000000:ℝ)],
  ![(38019433682056399245316405679/6544618791232234500000000000:ℝ)]]
theorem cell0_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 7 false b := by
 have heq : domainBranch cell0 7 false b = Record12518109.Bernstein.bsum 1 0 (4803731500949793904807405679/1454359731384941000000000000000:ℝ) cell0_domain7_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain7_0_g]
def cell0_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(4803731500949793904807405679/6544618791232234500000000000:ℝ)],
  ![(38019433682056399245316405679/6544618791232234500000000000:ℝ)]]
theorem cell0_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 7 true b := by
 have heq : domainBranch cell0 7 true b = Record12518109.Bernstein.bsum 1 0 (4803731500949793904807405679/1454359731384941000000000000000:ℝ) cell0_domain7_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain7_1_g]
def cell0_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(1508561467845063032021367926387/81807734890402931250000000000:ℝ)],
  ![(1346308448647131241973675426387/81807734890402931250000000000:ℝ)]]
theorem cell0_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 8 false b := by
 have heq : domainBranch cell0 8 false b = Record12518109.Bernstein.bsum 1 0 (1346308448647131241973675426387/18179496642311762500000000000000:ℝ) cell0_domain8_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain8_0_g]
def cell0_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(756796572474796938120132535439/40903867445201465625000000000:ℝ)],
  ![(675670062875831043096286285439/40903867445201465625000000000:ℝ)]]
theorem cell0_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell0 8 true b := by
 have heq : domainBranch cell0 8 true b = Record12518109.Bernstein.bsum 1 0 (675670062875831043096286285439/9089748321155881250000000000000:ℝ) cell0_domain8_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_domain8_1_g]
def cell0_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(6518829149646583559399/52356950329857876000000:ℝ)],
  ![(48726796538369992559399/52356950329857876000000:ℝ)]]
theorem cell0_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < ordinary cell0 0 b := by
 have heq : ordinary cell0 0 b = Record12518109.Bernstein.bsum 1 0 (6518829149646583559399/11634877851079528000000000:ℝ) cell0_ordinary0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordinary0_g]
def cell0_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(276453020655735922821803/157070850989573628000000:ℝ)],
  ![(149829118489565695821803/157070850989573628000000:ℝ)]]
theorem cell0_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < ordinary cell0 1 b := by
 have heq : ordinary cell0 1 b = Record12518109.Bernstein.bsum 1 0 (149829118489565695821803/34904633553238584000000000:ℝ) cell0_ordinary1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordinary1_g]
def cell0_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(2458941412029577906120679/21815395970774115000000:ℝ)],
  ![(2353421493557769383620679/21815395970774115000000:ℝ)]]
theorem cell0_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < ordinary cell0 2 b := by
 have heq : ordinary cell0 2 b = Record12518109.Bernstein.bsum 1 0 (7060264480673308150862037/14543597313849410000000000:ℝ) cell0_ordinary2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordinary2_g]
def cell0_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(194999989/90000000:ℝ)],
  ![(284999989/90000000:ℝ)]]
theorem cell0_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < ordinary cell0 3 b := by
 have heq : ordinary cell0 3 b = Record12518109.Bernstein.bsum 1 0 (194999989/20000000000:ℝ) cell0_ordinary3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordinary3_g]
def cell0_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(1790758342893276109149097/16361546978080586250000:ℝ)],
  ![(1678895310083258544774097/16361546978080586250000:ℝ)]]
theorem cell0_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < ordinary cell0 4 b := by
 have heq : ordinary cell0 4 b = Record12518109.Bernstein.bsum 1 0 (1678895310083258544774097/3635899328462352500000000:ℝ) cell0_ordinary4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordinary4_g]
def cell0_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(8113957645091211647/7388322670485000000000000:ℝ)],
  ![(8113957645091211647/7388322670485000000000000:ℝ)]]
theorem cell0_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < ordinary cell0 5 b := by
 have heq : ordinary cell0 5 b = Record12518109.Bernstein.bsum 1 0 (8113957645091211647/1641849482330000000000000000:ℝ) cell0_ordinary5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordinary5_g]
def cell0_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(2172749135251343194333/17452316776619292000000:ℝ)],
  ![(16242071598159146194333/17452316776619292000000:ℝ)]]
theorem cell0_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 0 false b := by
 have heq : complementBranch cell0 0 false b = Record12518109.Bernstein.bsum 1 0 (6518247405754029582999/11634877851079528000000000:ℝ) cell0_complement0_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement0_0_g]
def cell0_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(598106231780488700387141856199/4906238923035156915270000000000:ℝ)],
  ![(4555843880386400362601570856199/4906238923035156915270000000000:ℝ)]]
theorem cell0_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 0 true b := by
 have heq : complementBranch cell0 0 true b = Record12518109.Bernstein.bsum 1 0 (598106231780488700387141856199/1090275316230034870060000000000000:ℝ) cell0_complement0_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement0_1_g]
def cell0_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(15899759535759307276272323107/2181539597077411500000000000:ℝ)],
  ![(14217462365580149868309323107/2181539597077411500000000000:ℝ)]]
theorem cell0_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 1 false b := by
 have heq : complementBranch cell0 1 false b = Record12518109.Bernstein.bsum 1 0 (42652387096740449604927969321/1454359731384941000000000000000:ℝ) cell0_complement1_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement1_0_g]
def cell0_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(1787213574573710172237786389243993/245311946151757845763500000000000:ℝ)],
  ![(1598167667310589741537101452243993/245311946151757845763500000000000:ℝ)]]
theorem cell0_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 1 true b := by
 have heq : complementBranch cell0 1 true b = Record12518109.Bernstein.bsum 1 0 (1598167667310589741537101452243993/54513765811501743503000000000000000:ℝ) cell0_complement1_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement1_1_g]
def cell0_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(54991855879635482299117469321/6544618791232234500000000000:ℝ)],
  ![(28840980674736305575228469321/6544618791232234500000000000:ℝ)]]
theorem cell0_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 2 false b := by
 have heq : complementBranch cell0 2 false b = Record12518109.Bernstein.bsum 1 0 (28840980674736305575228469321/1454359731384941000000000000000:ℝ) cell0_complement2_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement2_0_g]
def cell0_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(2060561248473488611346060030743993/245311946151757845763500000000000:ℝ)],
  ![(1080474720394608410871875093743993/245311946151757845763500000000000:ℝ)]]
theorem cell0_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 2 true b := by
 have heq : complementBranch cell0 2 true b = Record12518109.Bernstein.bsum 1 0 (1080474720394608410871875093743993/54513765811501743503000000000000000:ℝ) cell0_complement2_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement2_1_g]
def cell0_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(31447089181865598661797344321/6544618791232234500000000000:ℝ)],
  ![(31676193594918552562908344321/6544618791232234500000000000:ℝ)]]
theorem cell0_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 3 false b := by
 have heq : complementBranch cell0 3 false b = Record12518109.Bernstein.bsum 1 0 (31447089181865598661797344321/1454359731384941000000000000000:ℝ) cell0_complement3_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement3_0_g]
def cell0_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(1178096121954157883302063010368993/245311946151757845763500000000000:ℝ)],
  ![(1186810369894977395044753073368993/245311946151757845763500000000000:ℝ)]]
theorem cell0_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 3 true b := by
 have heq : complementBranch cell0 3 true b = Record12518109.Bernstein.bsum 1 0 (1178096121954157883302063010368993/54513765811501743503000000000000000:ℝ) cell0_complement3_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement3_1_g]
def cell0_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(3582678792709312974447711869/727179865692470500000000000:ℝ)],
  ![(3315023953960173067626711869/727179865692470500000000000:ℝ)]]
theorem cell0_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 4 false b := by
 have heq : complementBranch cell0 4 false b = Record12518109.Bernstein.bsum 1 0 (29835215585641557608640406821/1454359731384941000000000000000:ℝ) cell0_complement4_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement4_0_g]
def cell0_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(1207907457221220432319252184056493/245311946151757845763500000000000:ℝ)],
  ![(1117741627560069972840254747056493/245311946151757845763500000000000:ℝ)]]
theorem cell0_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 4 true b := by
 have heq : complementBranch cell0 4 true b = Record12518109.Bernstein.bsum 1 0 (1117741627560069972840254747056493/54513765811501743503000000000000000:ℝ) cell0_complement4_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement4_1_g]
def cell0_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(121687/6000:ℝ)],
  ![(2367481/150000:ℝ)]]
theorem cell0_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 5 false b := by
 have heq : complementBranch cell0 5 false b = Record12518109.Bernstein.bsum 1 0 (7102443/100000000:ℝ) cell0_complement5_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement5_0_g]
def cell0_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(99490279595305426491308213563699/4906238923035156915270000000000:ℝ)],
  ![(77424747713577324906047293363699/4906238923035156915270000000000:ℝ)]]
theorem cell0_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 5 true b := by
 have heq : complementBranch cell0 5 true b = Record12518109.Bernstein.bsum 1 0 (77424747713577324906047293363699/1090275316230034870060000000000000:ℝ) cell0_complement5_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement5_1_g]
def cell0_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(1556455231454054292607807/52356950329857876000000:ℝ)],
  ![(1260999459732990429607807/52356950329857876000000:ℝ)]]
theorem cell0_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 6 false b := by
 have heq : complementBranch cell0 6 false b = Record12518109.Bernstein.bsum 1 0 (1260999459732990429607807/11634877851079528000000000:ℝ) cell0_complement6_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement6_0_g]
def cell0_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(145837558892223029191110873016199/4906238923035156915270000000000:ℝ)],
  ![(118153671708198550062385302016199/4906238923035156915270000000000:ℝ)]]
theorem cell0_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 6 true b := by
 have heq : complementBranch cell0 6 true b = Record12518109.Bernstein.bsum 1 0 (118153671708198550062385302016199/1090275316230034870060000000000000:ℝ) cell0_complement6_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement6_1_g]
def cell0_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(688090859403937138673823107/13089237582464469000000000000:ℝ)],
  ![(5439727562361642480710823107/13089237582464469000000000000:ℝ)]]
theorem cell0_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 7 false b := by
 have heq : complementBranch cell0 7 false b = Record12518109.Bernstein.bsum 1 0 (688090859403937138673823107/2908719462769882000000000000000:ℝ) cell0_complement7_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement7_0_g]
def cell0_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(8173821994539024364245739296527/163541297434505230509000000000000:ℝ)],
  ![(22542279885921335973666998765509/54513765811501743503000000000000:ℝ)]]
theorem cell0_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 7 true b := by
 have heq : complementBranch cell0 7 true b = Record12518109.Bernstein.bsum 1 0 (24521465983617073092737217889581/109027531623003487006000000000000000:ℝ) cell0_complement7_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement7_1_g]
def cell0_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(7206920009050520698072823107/13089237582464469000000000000:ℝ)],
  ![(54166524100731635040109823107/13089237582464469000000000000:ℝ)]]
theorem cell0_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 8 false b := by
 have heq : complementBranch cell0 8 false b = Record12518109.Bernstein.bsum 1 0 (7206920009050520698072823107/2908719462769882000000000000000:ℝ) cell0_complement8_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement8_0_g]
def cell0_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(268866738999819964649689934889581/490623892303515691527000000000000:ℝ)],
  ![(2029307033621014454866955705889581/490623892303515691527000000000000:ℝ)]]
theorem cell0_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 8 true b := by
 have heq : complementBranch cell0 8 true b = Record12518109.Bernstein.bsum 1 0 (268866738999819964649689934889581/109027531623003487006000000000000000:ℝ) cell0_complement8_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement8_1_g]
def cell0_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(2945542432154055529307524369/4363079194154823000000000000:ℝ)],
  ![(22116074411774711059986524369/4363079194154823000000000000:ℝ)]]
theorem cell0_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 9 false b := by
 have heq : complementBranch cell0 9 false b = Record12518109.Bernstein.bsum 1 0 (8836627296462166587922573107/2908719462769882000000000000000:ℝ) cell0_complement9_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement9_0_g]
def cell0_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(329953057253870687538928114139581/490623892303515691527000000000000:ℝ)],
  ![(2485913662282945062642943885139581/490623892303515691527000000000000:ℝ)]]
theorem cell0_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 9 true b := by
 have heq : complementBranch cell0 9 true b = Record12518109.Bernstein.bsum 1 0 (329953057253870687538928114139581/109027531623003487006000000000000000:ℝ) cell0_complement9_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement9_1_g]
def cell0_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(2172749135251343194333/17452316776619292000000:ℝ)],
  ![(16242071598159146194333/17452316776619292000000:ℝ)]]
theorem cell0_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 10 false b := by
 have heq : complementBranch cell0 10 false b = Record12518109.Bernstein.bsum 1 0 (6518247405754029582999/11634877851079528000000000:ℝ) cell0_complement10_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement10_0_g]
def cell0_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(598106231780488700387141856199/4906238923035156915270000000000:ℝ)],
  ![(4555843880386400362601570856199/4906238923035156915270000000000:ℝ)]]
theorem cell0_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 10 true b := by
 have heq : complementBranch cell0 10 true b = Record12518109.Bernstein.bsum 1 0 (598106231780488700387141856199/1090275316230034870060000000000000:ℝ) cell0_complement10_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement10_1_g]
def cell0_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(19556196576993473689997/26178475164928938000000:ℝ)],
  ![(146180098743163700689997/26178475164928938000000:ℝ)]]
theorem cell0_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 11 false b := by
 have heq : complementBranch cell0 11 false b = Record12518109.Bernstein.bsum 1 0 (19556196576993473689997/5817438925539764000000000:ℝ) cell0_complement11_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement11_0_g]
def cell0_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(3652422144483024844849050818699/4906238923035156915270000000000:ℝ)],
  ![(27386175313482930751400979818699/4906238923035156915270000000000:ℝ)]]
theorem cell0_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 11 true b := by
 have heq : complementBranch cell0 11 true b = Record12518109.Bernstein.bsum 1 0 (3652422144483024844849050818699/1090275316230034870060000000000000:ℝ) cell0_complement11_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement11_1_g]
def cell0_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(15210407434544510313131/17452316776619292000000:ℝ)],
  ![(113695664674899131313131/17452316776619292000000:ℝ)]]
theorem cell0_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 12 false b := by
 have heq : complementBranch cell0 12 false b = Record12518109.Bernstein.bsum 1 0 (45631222303633530939393/11634877851079528000000000:ℝ) cell0_complement12_0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement12_0_g]
def cell0_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(4263285327023532073741432611199/4906238923035156915270000000000:ℝ)],
  ![(31952241600102236829160861611199/4906238923035156915270000000000:ℝ)]]
theorem cell0_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ))
    (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell0 12 true b := by
 have heq : complementBranch cell0 12 true b = Record12518109.Bernstein.bsum 1 0 (4263285327023532073741432611199/1090275316230034870060000000000000:ℝ) cell0_complement12_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_complement12_1_g]
theorem cell0_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 0 b := complementReserve_pos_of_branches (cell0_complement0_0 hb hν) (cell0_complement0_1 hb hν)
theorem cell0_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 1 b := complementReserve_pos_of_branches (cell0_complement1_0 hb hν) (cell0_complement1_1 hb hν)
theorem cell0_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 2 b := complementReserve_pos_of_branches (cell0_complement2_0 hb hν) (cell0_complement2_1 hb hν)
theorem cell0_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 3 b := complementReserve_pos_of_branches (cell0_complement3_0 hb hν) (cell0_complement3_1 hb hν)
theorem cell0_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 4 b := complementReserve_pos_of_branches (cell0_complement4_0 hb hν) (cell0_complement4_1 hb hν)
theorem cell0_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 5 b := complementReserve_pos_of_branches (cell0_complement5_0 hb hν) (cell0_complement5_1 hb hν)
theorem cell0_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 6 b := complementReserve_pos_of_branches (cell0_complement6_0 hb hν) (cell0_complement6_1 hb hν)
theorem cell0_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 7 b := complementReserve_pos_of_branches (cell0_complement7_0 hb hν) (cell0_complement7_1 hb hν)
theorem cell0_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 8 b := complementReserve_pos_of_branches (cell0_complement8_0 hb hν) (cell0_complement8_1 hb hν)
theorem cell0_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 9 b := complementReserve_pos_of_branches (cell0_complement9_0 hb hν) (cell0_complement9_1 hb hν)
theorem cell0_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 10 b := complementReserve_pos_of_branches (cell0_complement10_0 hb hν) (cell0_complement10_1 hb hν)
theorem cell0_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 11 b := complementReserve_pos_of_branches (cell0_complement11_0 hb hν) (cell0_complement11_1 hb hν)
theorem cell0_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell0 12 b := complementReserve_pos_of_branches (cell0_complement12_0 hb hν) (cell0_complement12_1 hb hν)
theorem cell0_all_domains {b : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell0 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell0_domain0_0 (ν := (357/500:ℝ)) hb (by norm_num)
   | true => exact cell0_domain0_1 (ν := (357/500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell0_domain1_0 (ν := (357/500:ℝ)) hb (by norm_num)
   | true => exact cell0_domain1_1 (ν := (357/500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell0_domain2_0 (ν := (357/500:ℝ)) hb (by norm_num)
   | true => exact cell0_domain2_1 (ν := (357/500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell0_domain3_0 (ν := (357/500:ℝ)) hb (by norm_num)
   | true => exact cell0_domain3_1 (ν := (357/500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell0_domain4_0 (ν := (357/500:ℝ)) hb (by norm_num)
   | true => exact cell0_domain4_1 (ν := (357/500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell0_domain5_0 (ν := (357/500:ℝ)) hb (by norm_num)
   | true => exact cell0_domain5_1 (ν := (357/500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell0_domain6_0 (ν := (357/500:ℝ)) hb (by norm_num)
   | true => exact cell0_domain6_1 (ν := (357/500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell0_domain7_0 (ν := (357/500:ℝ)) hb (by norm_num)
   | true => exact cell0_domain7_1 (ν := (357/500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell0_domain8_0 (ν := (357/500:ℝ)) hb (by norm_num)
   | true => exact cell0_domain8_1 (ν := (357/500:ℝ)) hb (by norm_num)
end
end Record12518109Admission
