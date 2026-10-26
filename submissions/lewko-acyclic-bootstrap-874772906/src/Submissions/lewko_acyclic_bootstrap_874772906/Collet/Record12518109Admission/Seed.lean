/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def seedB : ℝ := (9981613/10000000:ℝ)
def seedL : ℝ := (4380251/1000000:ℝ)
def seedQ : ℝ := (183/250:ℝ)
def seedD (b : ℝ) : ℝ := seedB-1+(K-seedL)*b
def seedA (b : ℝ) : ℝ := seedQ*seedD b/(6*(incumbent-seedQ))+lowFee/(1-seedQ/incumbent)
def seedT (b : ℝ) : ℝ := seedB-(seedL-1)*(b-mesh)
def seedF (b : ℝ) : ℝ := 1-6*seedA b-pad
def seedRegular (j : ℕ) (b ν : ℝ) : ℝ := regular (seedT b) (seedA b) (retainedWidth b) (seedF b) ν j
def seedExceptional (j : ℕ) (b ν : ℝ) : ℝ := exceptional (seedT b) (seedA b) (seedF b) b (1/25) 0 0 ν j
def seed_regular0_g : Fin 2 → Fin 5 → ℝ := ![![(55053459470297756603160078929/286650773437500000:ℝ), (650500450140083734287268475693/573301546875000000:ℝ), (63547277956872829071241022093/28311187500000000:ℝ), (16999259281828402852853523568963/9172824750000000000:ℝ), (10112538885535912735297413151669/18345649500000000000:ℝ)],
  ![(256023399464944449115184236787/859952320312500000:ℝ), (2654805265232800806276305427079/1719904640625000000:ℝ), (6507335331479010753458022789533/2293206187500000000:ℝ), (61509899652765870206998070706889/27518474250000000000:ℝ), (35412208997384426682454739455007/55036948500000000000:ℝ)]]
theorem seed_regular0 {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < seedRegular 0 b ν := by
 have heq : seedRegular 0 b ν = Record12518109.Bernstein.bsum 1 4 (165160378410893269809480236787/2047973632812500000000000000:ℝ) seed_regular0_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_regular0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_regular0_g]
def seed_regular1_g : Fin 2 → Fin 5 → ℝ := ![![(3980327805485200106979148891/15086882812500000:ℝ), (45144259907512010405014459247/30173765625000000:ℝ), (116473861741016202262750070869/40231687500000000:ℝ), (1137829283506713582293069332577/482780250000000000:ℝ), (670164561642005478139418455351/965560500000000000:ℝ)],
  ![(18347413754692425547553446673/45260648437500000:ℝ), (187125985673334207710543377741/90521296875000000:ℝ), (453621545053204809350750212607/120695062500000000:ℝ), (4253052630410118004691707997731/1448340750000000000:ℝ), (2432995068455792801605755366053/2896681500000000000:ℝ)]]
theorem seed_regular1 {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < seedRegular 1 b ν := by
 have heq : seedRegular 1 b ν = Record12518109.Bernstein.bsum 1 4 (11940983416455600320937446673/107788085937500000000000000:ℝ) seed_regular1_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_regular1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_regular1_g]
def seed_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(9892733869118047095598891/15086882812500000:ℝ), (1201822973411685833415456583/3352640625000000:ℝ), (42852084570474922715418120869/40231687500000000:ℝ), (510414570295042617110507482577/482780250000000000:ℝ), (112624738690521024899509385117/321853500000000000:ℝ)],
  ![(480455522968911367902796673/45260648437500000:ℝ), (34573922535277443997717327741/90521296875000000:ℝ), (129894652732549720708754362607/120695062500000000:ℝ), (1519085630435261359144022447731/1448340750000000000:ℝ), (996325358892903091283084466053/2896681500000000000:ℝ)]]
theorem seed_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < seedRegular 2 b ν := by
 have heq : seedRegular 2 b ν = Record12518109.Bernstein.bsum 1 4 (29678201607354141286796673/107788085937500000000000000:ℝ) seed_regular2_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_regular2_g]
def seed_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(285532656893506938022099/1676320312500000:ℝ), (10590257672610208765753809247/30173765625000000:ℝ), (42106752312400092279247520869/40231687500000000:ℝ), (167481305627884190858610060859/160926750000000000:ℝ), (333052065924501589833533255351/965560500000000000:ℝ)],
  ![(8130983403111507542596673/45260648437500000:ℝ), (30483522406040553592761427741/90521296875000000:ℝ), (121209915917880204400242562607/120695062500000000:ℝ), (1446530319764844350539990547731/1448340750000000000:ℝ), (958982352099765511688099766053/2896681500000000000:ℝ)]]
theorem seed_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < seedRegular 3 b ν := by
 have heq : seedRegular 3 b ν = Record12518109.Bernstein.bsum 1 4 (7709381736124687326596673/107788085937500000000000000:ℝ) seed_regular3_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_regular3_g]
def seed_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(3953650798586321532586996673/45260648437500000:ℝ), (57691458874331726430575227741/90521296875000000:ℝ), (167555167614378002930695162607/120695062500000000:ℝ), (1758019646737250797446111347731/1448340750000000000:ℝ), (1087810998772397316391160166053/2896681500000000000:ℝ)],
  ![(2959043861981384269602996673/45260648437500000:ℝ), (48886069467175428126075227741/90521296875000000:ℝ), (148274662843312355493195162607/120695062500000000:ℝ), (1590634606989271805258611347731/1448340750000000000:ℝ), (997655417292798683578660166053/2896681500000000000:ℝ)]]
theorem seed_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < seedRegular 4 b ν := by
 have heq : seedRegular 4 b ν = Record12518109.Bernstein.bsum 1 4 (2959043861981384269602996673/107788085937500000000000000:ℝ) seed_regular4_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_regular4_g]
def seed_exceptional0_g : Fin 2 → Fin 3 → ℝ := ![![(266245995748292274205039/679468500000000000:ℝ), (1114570941043333099006219/1358937000000000000:ℝ), (1164740888229058614195469/2717874000000000000:ℝ)],
  ![(253285721513652762205039/679468500000000000:ℝ), (1061775662173277599006219/1358937000000000000:ℝ), (1110980877970746114195469/2717874000000000000:ℝ)]]
theorem seed_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < seedExceptional 0 b ν := by
 have heq : seedExceptional 0 b ν = Record12518109.Bernstein.bsum 1 2 (253285721513652762205039/524281250000000000000000:ℝ) seed_exceptional0_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_exceptional0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_exceptional0_g]
def seed_exceptional1_g : Fin 2 → Fin 3 → ℝ := ![![(18185212893768325451581/35761500000000000:ℝ), (84531080982495183664801/71523000000000000:ℝ), (96351994028630829365551/143046000000000000:ℝ)],
  ![(17343068121468877451581/35761500000000000:ℝ), (80932785014335683664801/71523000000000000:ℝ), (92523425946943329365551/143046000000000000:ℝ)]]
theorem seed_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < seedExceptional 1 b ν := by
 have heq : seedExceptional 1 b ν = Record12518109.Bernstein.bsum 1 2 (17343068121468877451581/27593750000000000000000:ℝ) seed_exceptional1_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_exceptional1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_exceptional1_g]
def seed_exceptional2_g : Fin 2 → Fin 3 → ℝ := ![![(20620542074784721417807/95364000000000000:ℝ), (146129035828750710721/381456000000000:ℝ), (340394015223889523/2034432000000:ℝ)],
  ![(58594722597052980253421/286092000000000000:ℝ), (413369620961700132163/1144368000000000:ℝ), (2872187780959005707/18309888000000:ℝ)]]
theorem seed_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < seedExceptional 2 b ν := by
 have heq : seedExceptional 2 b ν = Record12518109.Bernstein.bsum 1 2 (2872187780959005707/14128000000000000000:ℝ) seed_exceptional2_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_exceptional2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_exceptional2_g]
def seed_exceptional3_g : Fin 2 → Fin 3 → ℝ := ![![(25557552392032474911671/75496500000000000:ℝ), (107360105047037011000691/150993000000000000:ℝ), (112557796956562068243941/301986000000000000:ℝ)],
  ![(72352565764550920735013/226489500000000000:ℝ), (304481888851092533002073/452979000000000000:ℝ), (319753387450248704731823/905958000000000000:ℝ)]]
theorem seed_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < seedExceptional 3 b ν := by
 have heq : seedExceptional 3 b ν = Record12518109.Bernstein.bsum 1 2 (217057697293652762205039/524281250000000000000000:ℝ) seed_exceptional3_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_exceptional3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_exceptional3_g]
def seed_exceptional4_g : Fin 2 → Fin 3 → ℝ := ![![(5371493587922775150527/11920500000000000:ℝ), (25233455250831727888267/23841000000000000:ℝ), (9663880283181203262839/15894000000000000:ℝ)],
  ![(5090778663822959150527/11920500000000000:ℝ), (2670447029049469765363/2649000000000000:ℝ), (27715451488981109788517/47682000000000000:ℝ)]]
theorem seed_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < seedExceptional 4 b ν := by
 have heq : seedExceptional 4 b ν = Record12518109.Bernstein.bsum 1 2 (15272335991468877451581/27593750000000000000000:ℝ) seed_exceptional4_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_exceptional4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_exceptional4_g]
def seed_gate_natural_defect_g : Fin 2 → Fin 1 → ℝ := ![![(11161/2000000:ℝ)],
  ![(246579/2000000:ℝ)]]
theorem seed_gate_natural_defect {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (seedD b) := by
 have heq : (seedD b) = Record12518109.Bernstein.bsum 1 0 (11161/500000000:ℝ) seed_gate_natural_defect_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_natural_defect_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_natural_defect_g]
def seed_gate_amplifier_positive_g : Fin 2 → Fin 1 → ℝ := ![![(27270323/706400000:ℝ)],
  ![(601690243/706400000:ℝ)]]
theorem seed_gate_amplifier_positive {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (seedA b) := by
 have heq : (seedA b) = Record12518109.Bernstein.bsum 1 0 (27270323/176600000000:ℝ) seed_gate_amplifier_positive_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_amplifier_positive_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_amplifier_positive_g]
def seed_gate_amplifier_below_g : Fin 2 → Fin 1 → ℝ := ![![(4311818911/2119200000:ℝ)],
  ![(2588559151/2119200000:ℝ)]]
theorem seed_gate_amplifier_below {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (1/75-seedA b) := by
 have heq : (1/75-seedA b) = Record12518109.Bernstein.bsum 1 0 (2588559151/529800000000:ℝ) seed_gate_amplifier_below_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_amplifier_below_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_amplifier_below_g]
def seed_gate_centered_exception_g : Fin 2 → Fin 1 → ℝ := ![![(60835276041238367/7064000000000000:ℝ)],
  ![(33015576305238367/7064000000000000:ℝ)]]
theorem seed_gate_centered_exception {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (1-seedT b-9*seedA b) := by
 have heq : (1-seedT b-9*seedA b) = Record12518109.Bernstein.bsum 1 0 (33015576305238367/1766000000000000000:ℝ) seed_gate_centered_exception_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_centered_exception_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_centered_exception_g]
def seed_gate_reference_four_g : Fin 2 → Fin 1 → ℝ := ![![(30628942323238367/7064000000000000:ℝ)],
  ![(31530238587238367/7064000000000000:ℝ)]]
theorem seed_gate_reference_four {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (49/50-seedT b-4*seedA b) := by
 have heq : (49/50-seedT b-4*seedA b) = Record12518109.Bernstein.bsum 1 0 (30628942323238367/1766000000000000000:ℝ) seed_gate_reference_four_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_reference_four_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_reference_four_g]
def seed_gate_reference_four_half_g : Fin 2 → Fin 1 → ℝ := ![![(31477992376238367/7064000000000000:ℝ)],
  ![(29507189040238367/7064000000000000:ℝ)]]
theorem seed_gate_reference_four_half {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (49/50-seedT b-9/2*seedA b) := by
 have heq : (49/50-seedT b-9/2*seedA b) = Record12518109.Bernstein.bsum 1 0 (29507189040238367/1766000000000000000:ℝ) seed_gate_reference_four_half_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_reference_four_half_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_reference_four_half_g]
def seed_gate_error_one_g : Fin 2 → Fin 1 → ℝ := ![![(340813073/42384000000:ℝ)],
  ![(2703734979/14128000000:ℝ)]]
theorem seed_gate_error_one {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (seedA b/4-(seedD b+(9/2-K)*b)/6) := by
 have heq : (seedA b/4-(seedD b+(9/2-K)*b)/6) = Record12518109.Bernstein.bsum 1 0 (340813073/10596000000000:ℝ) seed_gate_error_one_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_error_one_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_error_one_g]
def seed_gate_error_six_g : Fin 2 → Fin 1 → ℝ := ![![(5249471213/42384000000:ℝ)],
  ![(38805149559/14128000000:ℝ)]]
theorem seed_gate_error_six {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (13/4*seedA b-(seedD b+(9/2-K)*b)/6) := by
 have heq : (13/4*seedA b-(seedD b+(9/2-K)*b)/6) = Record12518109.Bernstein.bsum 1 0 (5249471213/10596000000000:ℝ) seed_gate_error_six_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_error_six_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_error_six_g]
def seed_gate_error_seven_g : Fin 2 → Fin 1 → ℝ := ![![(1619158937/10596000000:ℝ)],
  ![(11957625801/3532000000:ℝ)]]
theorem seed_gate_error_seven {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (4*seedA b-(seedD b+(9/2-K)*b)/6) := by
 have heq : (4*seedA b-(seedD b+(9/2-K)*b)/6) = Record12518109.Bernstein.bsum 1 0 (1619158937/2649000000000:ℝ) seed_gate_error_seven_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_error_seven_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_error_seven_g]
def seed_gate_conserved_width_g : Fin 2 → Fin 1 → ℝ := ![![(8774043800743/70640000000:ℝ)],
  ![(8288111848743/70640000000:ℝ)]]
theorem seed_gate_conserved_width {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (seedF b-2*retainedWidth b) := by
 have heq : (seedF b-2*retainedWidth b) = Record12518109.Bernstein.bsum 1 0 (8288111848743/17660000000000:ℝ) seed_gate_conserved_width_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_conserved_width_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_conserved_width_g]
def seed_gate_reference_capacity_g : Fin 2 → Fin 1 → ℝ := ![![(1225153/50000:ℝ)],
  ![(200051/10000:ℝ)]]
theorem seed_gate_reference_capacity {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (1-1/4-1/2-K*b) := by
 have heq : (1-1/4-1/2-K*b) = Record12518109.Bernstein.bsum 1 0 (200051/2500000:ℝ) seed_gate_reference_capacity_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_reference_capacity_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_reference_capacity_g]
def seed_gate_low_g : Fin 2 → Fin 1 → ℝ := ![![(1/800000:ℝ)],
  ![(1/800000:ℝ)]]
theorem seed_gate_low {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (seedA b-seedQ*(seedD b+6*seedA b)/K) := by
 have heq : (seedA b-seedQ*(seedD b+6*seedA b)/K) = Record12518109.Bernstein.bsum 1 0 (1/200000000:ℝ) seed_gate_low_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_low_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_low_g]
def seed_gate_forced_prime_g : Fin 2 → Fin 1 → ℝ := ![![(23894577459/706400000:ℝ)],
  ![(19873638019/706400000:ℝ)]]
theorem seed_gate_forced_prime {b ν : ℝ} (hb : b ∈ Set.Icc (2/125:ℝ) (1/50:ℝ))
    (hν : ν ∈ Set.Icc (183/250:ℝ) (3/4:ℝ)) : 0 < (1/4-7*seedA b) := by
 have heq : (1/4-7*seedA b) = Record12518109.Bernstein.bsum 1 0 (19873638019/176600000000:ℝ) seed_gate_forced_prime_g (2/125:ℝ) (1/50:ℝ) (183/250:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, seedRegular, seedExceptional, seedD, seedA, seedT, seedF, seedB, seedL, seedQ, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, seed_gate_forced_prime_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seed_gate_forced_prime_g]
end
end Record12518109Admission
