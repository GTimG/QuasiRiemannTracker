/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell4 : Cell := ⟨(306003/312500:ℝ), (74001/20000:ℝ), (1271/2000:ℝ), (3/80:ℝ), (39/1000:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (471/100000:ℝ), (1/25:ℝ)⟩
def cell4_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(4622974614086163206027601642501245512399547/104597646145601038637310517500000000:ℝ), (88142429759847530672405077341842362984293953/26149411536400259659327629375000000:ℝ), (168938280350488309085080982742444941756600453/17432941024266839772885086250000000:ℝ), (244236843340474391829949639176218476112600453/26149411536400259659327629375000000:ℝ), (312059962289255793765117595657645879487600453/104597646145601038637310517500000000:ℝ)],
  ![(6056851157343489992468265711343212871399547/104597646145601038637310517500000000:ℝ), (87743457480870810115486126233623822734293953/26149411536400259659327629375000000:ℝ), (166868839819883922657265449517541441756600453/17432941024266839772885086250000000:ℝ), (240680240397205503325453192968780976112600453/26149411536400259659327629375000000:ℝ), (307211542099782705376291499970145879487600453/104597646145601038637310517500000000:ℝ)]]
theorem cell4_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highRegular cell4 2 b ν := by
 have heq : highRegular cell4 2 b ν = Record12518109.Bernstein.bsum 1 4 (4622974614086163206027601642501245512399547/405703454403403920000000000000000000000000:ℝ) cell4_regular2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_regular2_g]
def cell4_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(8304724362042439228529774814023543493547/104597646145601038637310517500000000:ℝ), (27462508113001001240110421559378178990066651/8716470512133419886442543125000000:ℝ), (163014509427365087152287762891218691725506453/17432941024266839772885086250000000:ℝ), (239172792340025354946430747595551448081506453/26149411536400259659327629375000000:ℝ), (102925506245820753777299118891527700485502151/34865882048533679545770172500000000:ℝ)],
  ![(8388251115140239326519552402030902493547/104597646145601038637310517500000000:ℝ), (26937500751117788073875232577625332240066651/8716470512133419886442543125000000:ℝ), (160015023780618482367046393456315191725506453/17432941024266839772885086250000000:ℝ), (234912099671199196958916761388113948081506453/26149411536400259659327629375000000:ℝ), (101141813969212324499932920329027700485502151/34865882048533679545770172500000000:ℝ)]]
theorem cell4_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highRegular cell4 3 b ν := by
 have heq : highRegular cell4 3 b ν = Record12518109.Bernstein.bsum 1 4 (8304724362042439228529774814023543493547/405703454403403920000000000000000000000000:ℝ) cell4_regular3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_regular3_g]
def cell4_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(36057716035041625473924308961058908787245547/104597646145601038637310517500000000:ℝ), (31495742011038398928376149042206738204482651/8716470512133419886442543125000000:ℝ), (155165034380661034737833566364479483122754453/17432941024266839772885086250000000:ℝ), (216764209940186994030007884908285435478754453/26149411536400259659327629375000000:ℝ), (92725930333506191745447166048719529617918151/34865882048533679545770172500000000:ℝ)],
  ![(32814286974101276666396893044738536146245547/104597646145601038637310517500000000:ℝ), (30089426421349621072520322288388891454482651/8716470512133419886442543125000000:ℝ), (150094866044995474950736974699575983122754453/17432941024266839772885086250000000:ℝ), (210956456871587845815712397450847935478754453/26149411536400259659327629375000000:ℝ), (90578728804774841552627217486219529617918151/34865882048533679545770172500000000:ℝ)]]
theorem cell4_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highRegular cell4 4 b ν := by
 have heq : highRegular cell4 4 b ν = Record12518109.Bernstein.bsum 1 4 (32814286974101276666396893044738536146245547/405703454403403920000000000000000000000000:ℝ) cell4_regular4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_regular4_g]
def cell4_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(3027094007877874280047520532947228071/151587900823128447902130000000000:ℝ), (4137491154959845396325967638927669929/75793950411564223951065000000000:ℝ), (5320964331109883768302784132740271929/151587900823128447902130000000000:ℝ)],
  ![(2958987731899663114195097061734228071/151587900823128447902130000000000:ℝ), (4061414105147966103114870791927669929/75793950411564223951065000000000:ℝ), (5236488734191086626164822382740271929/151587900823128447902130000000000:ℝ)]]
theorem cell4_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 0 false b ν := by
 have heq : highBranch cell4 0 false b ν = Record12518109.Bernstein.bsum 1 2 (2958987731899663114195097061734228071/7708365633664674480000000000000000000:ℝ) cell4_exceptional0_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional0_0_g]
def cell4_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(113343617807835869955937947544883865710293/5681969286553323612715538790000000000:ℝ), (17219098856866419235486326193943387716523/315664960364073534039752155000000000:ℝ), (199339270413318041228157903710209971789707/5681969286553323612715538790000000000:ℝ)],
  ![(110796384645610033023454774089211986710293/5681969286553323612715538790000000000:ℝ), (16902857361881750446304663496226887716523/315664960364073534039752155000000000:ℝ), (196178122440218620641830625592459971789707/5681969286553323612715538790000000000:ℝ)]]
theorem cell4_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 0 true b ν := by
 have heq : highBranch cell4 0 true b ν = Record12518109.Bernstein.bsum 1 2 (110796384645610033023454774089211986710293/288932669046652993533840000000000000000000:ℝ) cell4_exceptional0_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional0_1_g]
theorem cell4_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell4 0 b ν :=
 highExceptional_pos_of_branches (cell4_exceptional0_0 hb hν) (cell4_exceptional0_1 hb hν)
def cell4_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(42630255609144296542154648903854109/7978310569638339363270000000000:ℝ), (307048359725134620597106335154087891/3989155284819169681635000000000:ℝ), (63923618959353457333844864295405099/886478952182037707030000000000:ℝ)],
  ![(40707078868146939240715913576854109/7978310569638339363270000000000:ℝ), (303228877741041704971031172154087891/3989155284819169681635000000000:ℝ), (63286029891576669458805614295405099/886478952182037707030000000000:ℝ)]]
theorem cell4_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 1 false b ν := by
 have heq : highBranch cell4 1 false b ν = Record12518109.Bernstein.bsum 1 2 (40707078868146939240715913576854109/405703454403403920000000000000000000:ℝ) cell4_exceptional1_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional1_0_g]
def cell4_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(1591544245237003473443095094780159142647/299051015081753874353449410000000000:ℝ), (1278123324177807525274129176529809879817/16613945282319659686302745000000000:ℝ), (21558839210887656452298702701920253357353/299051015081753874353449410000000000:ℝ)],
  ![(1519752252520802276932383584613218142647/299051015081753874353449410000000000:ℝ), (1262247741617873677747610155926309879817/16613945282319659686302745000000000:ℝ), (21344026810914457903145728524670253357353/299051015081753874353449410000000000:ℝ)]]
theorem cell4_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 1 true b ν := by
 have heq : highBranch cell4 1 true b ν = Record12518109.Bernstein.bsum 1 2 (1519752252520802276932383584613218142647/15206982581402789133360000000000000000000:ℝ) cell4_exceptional1_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional1_1_g]
theorem cell4_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell4 1 b ν :=
 highExceptional_pos_of_branches (cell4_exceptional1_0 hb hν) (cell4_exceptional1_1 hb hν)
def cell4_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(128617085665972255201027928892195109/3989155284819169681635000000000:ℝ), (21698683267475501706837784112899/498644410602396210204375000:ℝ), (395541351951837218547913100471/31913242278553357453080000:ℝ)],
  ![(126687362784415608126037073728695109/3989155284819169681635000000000:ℝ), (21291153400055024542761982487899/498644410602396210204375000:ℝ), (384661062305194333946500100471/31913242278553357453080000:ℝ)]]
theorem cell4_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 2 false b ν := by
 have heq : highBranch cell4 2 false b ν = Record12518109.Bernstein.bsum 1 2 (384661062305194333946500100471/1622813817613615680000000000000:ℝ) cell4_exceptional2_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional2_0_g]
def cell4_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(535287221299298753923726173654232066183/16613945282319659686302745000000000:ℝ), (6500297374453974268518330141944841311/149525507540876937176724705000000:ℝ), (14802177658887911911517179884894943/1196204060327015497413797640000:ℝ)],
  ![(527266712161955817401245737982457566183/16613945282319659686302745000000000:ℝ), (6378379238460150432863408112763341311/149525507540876937176724705000000:ℝ), (14395457199159186708513983175894943/1196204060327015497413797640000:ℝ)]]
theorem cell4_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 2 true b ν := by
 have heq : highBranch cell4 2 true b ν = Record12518109.Bernstein.bsum 1 2 (14395457199159186708513983175894943/60827930325611156533440000000000000:ℝ) cell4_exceptional2_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional2_1_g]
theorem cell4_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell4 2 b ν :=
 highExceptional_pos_of_branches (cell4_exceptional2_0 hb hν) (cell4_exceptional2_1 hb hν)
def cell4_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(2563231027404092479873148932947228071/151587900823128447902130000000000:ℝ), (3590305966094296332853939238927669929/75793950411564223951065000000000:ℝ), (1564833092624839177825718577580090643/50529300274376149300710000000000:ℝ)],
  ![(2495124751425881314020725461734228071/151587900823128447902130000000000:ℝ), (3514228916282417039642842391927669929/75793950411564223951065000000000:ℝ), (1536674560318573463779731327580090643/50529300274376149300710000000000:ℝ)]]
theorem cell4_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 3 false b ν := by
 have heq : highBranch cell4 3 false b ν = Record12518109.Bernstein.bsum 1 2 (2495124751425881314020725461734228071/7708365633664674480000000000000000000:ℝ) cell4_exceptional3_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional3_0_g]
def cell4_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(95956641710737106740001976862083865710293/5681969286553323612715538790000000000:ℝ), (44820582425850132524418298409430163149569/946994881092220602119256465000000000:ℝ), (175857480822896808648188874393009971789707/5681969286553323612715538790000000000:ℝ)],
  ![(93409408548511269807518803406411986710293/5681969286553323612715538790000000000:ℝ), (43871857940896126156873310316280663149569/946994881092220602119256465000000000:ℝ), (172696332849797388061861596275259971789707/5681969286553323612715538790000000000:ℝ)]]
theorem cell4_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 3 true b ν := by
 have heq : highBranch cell4 3 true b ν = Record12518109.Bernstein.bsum 1 2 (93409408548511269807518803406411986710293/288932669046652993533840000000000000000000:ℝ) cell4_exceptional3_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional3_1_g]
theorem cell4_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell4 3 b ν :=
 highExceptional_pos_of_branches (cell4_exceptional3_0 hb hν) (cell4_exceptional3_1 hb hν)
def cell4_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(23054944251661008397998248903854109/7978310569638339363270000000000:ℝ), (274485705898600462472262735154087891/3989155284819169681635000000000:ℝ), (176658443095706592316253392886215297/2659436856546113121090000000000:ℝ)],
  ![(21131767510663651096559513576854109/7978310569638339363270000000000:ℝ), (270666223914507546846187572154087891/3989155284819169681635000000000:ℝ), (174745675892376228691135642886215297/2659436856546113121090000000000:ℝ)]]
theorem cell4_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 4 false b ν := by
 have heq : highBranch cell4 4 false b ν = Record12518109.Bernstein.bsum 1 2 (21131767510663651096559513576854109/405703454403403920000000000000000000:ℝ) cell4_exceptional4_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional4_0_g]
def cell4_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(857802849624457383935680753580159142647/299051015081753874353449410000000000:ℝ), (3427521321406762626157883309989429639451/49841835846958979058908235000000000:ℝ), (19859463393475756280468517043120253357353/299051015081753874353449410000000000:ℝ)],
  ![(786010856908256187424969243413218142647/299051015081753874353449410000000000:ℝ), (3379894573726961083578326248178929639451/49841835846958979058908235000000000:ℝ), (19644650993502557731315542865870253357353/299051015081753874353449410000000000:ℝ)]]
theorem cell4_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 4 true b ν := by
 have heq : highBranch cell4 4 true b ν = Record12518109.Bernstein.bsum 1 2 (786010856908256187424969243413218142647/15206982581402789133360000000000000000000:ℝ) cell4_exceptional4_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional4_1_g]
theorem cell4_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell4 4 b ν :=
 highExceptional_pos_of_branches (cell4_exceptional4_0 hb hν) (cell4_exceptional4_1 hb hν)
def cell4_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(150551324334248094728753459759854109/7978310569638339363270000000000:ℝ), (626655482030172868751550319224737781539/14875560057090683742816915000000000:ℝ), (725244487401197584703367717285054527539/29751120114181367485633830000000000:ℝ)],
  ![(147091636759823784593464724432854109/7978310569638339363270000000000:ℝ), (613284613589002854917698763285237781539/14875560057090683742816915000000000:ℝ), (711183764219928855992625860535054527539/29751120114181367485633830000000000:ℝ)]]
theorem cell4_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 5 false b ν := by
 have heq : highBranch cell4 5 false b ν = Record12518109.Bernstein.bsum 1 2 (147091636759823784593464724432854109/405703454403403920000000000000000000:ℝ) cell4_exceptional5_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional5_0_g]
def cell4_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(5636749664260069140871378322095607142647/299051015081753874353449410000000000:ℝ), (23466614029272910946395065128812453277926337/557580617619930098732006424945000000000:ℝ), (27163449732392070812251293471618436381569337/1115161235239860197464012849890000000000:ℝ)],
  ![(5507364635974525471289467261928666142647/299051015081753874353449410000000000:ℝ), (22966498024727770947684304230262552277926337/557580617619930098732006424945000000000:ℝ), (26637442189121684669253464576390686381569337/1115161235239860197464012849890000000000:ℝ)]]
theorem cell4_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 5 true b ν := by
 have heq : highBranch cell4 5 true b ν = Record12518109.Bernstein.bsum 1 2 (5507364635974525471289467261928666142647/15206982581402789133360000000000000000000:ℝ) cell4_exceptional5_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional5_1_g]
theorem cell4_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell4 5 b ν :=
 highExceptional_pos_of_branches (cell4_exceptional5_0 hb hν) (cell4_exceptional5_1 hb hν)
def cell4_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(128617085665972255201027928892195109/3989155284819169681635000000000:ℝ), (21698683267475501706837784112899/498644410602396210204375000:ℝ), (395541351951837218547913100471/31913242278553357453080000:ℝ)],
  ![(126687362784415608126037073728695109/3989155284819169681635000000000:ℝ), (21291153400055024542761982487899/498644410602396210204375000:ℝ), (384661062305194333946500100471/31913242278553357453080000:ℝ)]]
theorem cell4_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 6 false b ν := by
 have heq : highBranch cell4 6 false b ν = Record12518109.Bernstein.bsum 1 2 (384661062305194333946500100471/1622813817613615680000000000000:ℝ) cell4_exceptional6_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional6_0_g]
def cell4_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(535287221299298753923726173654232066183/16613945282319659686302745000000000:ℝ), (6500297374453974268518330141944841311/149525507540876937176724705000000:ℝ), (14802177658887911911517179884894943/1196204060327015497413797640000:ℝ)],
  ![(527266712161955817401245737982457566183/16613945282319659686302745000000000:ℝ), (6378379238460150432863408112763341311/149525507540876937176724705000000:ℝ), (14395457199159186708513983175894943/1196204060327015497413797640000:ℝ)]]
theorem cell4_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 6 true b ν := by
 have heq : highBranch cell4 6 true b ν = Record12518109.Bernstein.bsum 1 2 (14395457199159186708513983175894943/60827930325611156533440000000000000:ℝ) cell4_exceptional6_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional6_1_g]
theorem cell4_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell4 6 b ν :=
 highExceptional_pos_of_branches (cell4_exceptional6_0 hb hν) (cell4_exceptional6_1 hb hν)
def cell4_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(126501103874695261346997059759854109/7978310569638339363270000000000:ℝ), (19518346737481779097607515526842140057/550946668781136434919145000000000:ℝ), (205202506419513478050547510961684842513/9917040038060455828544610000000000:ℝ)],
  ![(123041416300270951211708324432854109/7978310569638339363270000000000:ℝ), (57069388163426446866839040365026420171/1652840006343409304757435000000000:ℝ), (200515598692423901813633558711684842513/9917040038060455828544610000000000:ℝ)]]
theorem cell4_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 7 false b ν := by
 have heq : highBranch cell4 7 false b ν = Record12518109.Bernstein.bsum 1 2 (123041416300270951211708324432854109/405703454403403920000000000000000000:ℝ) cell4_exceptional7_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional7_0_g]
def cell4_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(4735275250774650287223003180895607142647/299051015081753874353449410000000000:ℝ), (6577017915627912835567504044870817759308779/185860205873310032910668808315000000000:ℝ), (7684642418500284279373659461584412127189779/371720411746620065821337616630000000000:ℝ)],
  ![(4605890222489106617641092120728666142647/299051015081753874353449410000000000:ℝ), (6410312580779532835997250412020850759308779/185860205873310032910668808315000000000:ℝ), (7509306570743488898374383163175162127189779/371720411746620065821337616630000000000:ℝ)]]
theorem cell4_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell4 7 true b ν := by
 have heq : highBranch cell4 7 true b ν = Record12518109.Bernstein.bsum 1 2 (4605890222489106617641092120728666142647/15206982581402789133360000000000000000000:ℝ) cell4_exceptional7_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_exceptional7_1_g]
theorem cell4_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell4 7 b ν :=
 highExceptional_pos_of_branches (cell4_exceptional7_0 hb hν) (cell4_exceptional7_1 hb hν)
def cell4_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(759881905955471810076418687/304139651628055782667200000000:ℝ)],
  ![(3918273609927016128838618687/304139651628055782667200000000:ℝ)]]
theorem cell4_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 0 false b := by
 have heq : domainBranch cell4 0 false b = Record12518109.Bernstein.bsum 1 0 (759881905955471810076418687/202759767752037188444800000000000:ℝ) cell4_domain0_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain0_0_g]
def cell4_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(759881905955471810076418687/304139651628055782667200000000:ℝ)],
  ![(3918273609927016128838618687/304139651628055782667200000000:ℝ)]]
theorem cell4_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 0 true b := by
 have heq : domainBranch cell4 0 true b = Record12518109.Bernstein.bsum 1 0 (759881905955471810076418687/202759767752037188444800000000000:ℝ) cell4_domain0_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain0_1_g]
def cell4_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(13806136162517008645701305869331/4226077650035457500000000000000:ℝ)],
  ![(12194474449038102216683237119331/4226077650035457500000000000000:ℝ)]]
theorem cell4_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 1 false b := by
 have heq : domainBranch cell4 1 false b = Record12518109.Bernstein.bsum 1 0 (36583423347114306650049711357993/8452155300070915000000000000000000:ℝ) cell4_domain1_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain1_0_g]
def cell4_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(162689791811454906245585436470789/25356465900212745000000000000000:ℝ)],
  ![(153019821530581467671477023970789/25356465900212745000000000000000:ℝ)]]
theorem cell4_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 1 true b := by
 have heq : domainBranch cell4 1 true b = Record12518109.Bernstein.bsum 1 0 (153019821530581467671477023970789/16904310600141830000000000000000000:ℝ) cell4_domain1_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain1_1_g]
def cell4_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(11315695940952338168371908217601/1267823295010637250000000000000:ℝ)],
  ![(11551246862506014105641526967601/1267823295010637250000000000000:ℝ)]]
theorem cell4_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 2 false b := by
 have heq : domainBranch cell4 2 false b = Record12518109.Bernstein.bsum 1 0 (11315695940952338168371908217601/845215530007091500000000000000000:ℝ) cell4_domain2_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain2_0_g]
def cell4_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(15028726959541871533451940648473/2535646590021274500000000000000:ℝ)],
  ![(15499828802649223407991178148473/2535646590021274500000000000000:ℝ)]]
theorem cell4_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 2 true b := by
 have heq : domainBranch cell4 2 true b = Record12518109.Bernstein.bsum 1 0 (15028726959541871533451940648473/1690431060014183000000000000000000:ℝ) cell4_domain2_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain2_1_g]
def cell4_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(157793763859952868039505984133/25356465900212745000000000000:ℝ)],
  ![(282194411242398780809208484133/25356465900212745000000000000:ℝ)]]
theorem cell4_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 3 false b := by
 have heq : domainBranch cell4 3 false b = Record12518109.Bernstein.bsum 1 0 (157793763859952868039505984133/16904310600141830000000000000000:ℝ) cell4_domain3_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain3_0_g]
def cell4_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(157793763859952868039505984133/25356465900212745000000000000:ℝ)],
  ![(282194411242398780809208484133/25356465900212745000000000000:ℝ)]]
theorem cell4_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 3 true b := by
 have heq : domainBranch cell4 3 true b = Record12518109.Bernstein.bsum 1 0 (157793763859952868039505984133/16904310600141830000000000000000:ℝ) cell4_domain3_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain3_1_g]
def cell4_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(731965184631742753900967/105651941250886437500000:ℝ)],
  ![(499793707837098928900967/105651941250886437500000:ℝ)]]
theorem cell4_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 4 false b := by
 have heq : domainBranch cell4 4 false b = Record12518109.Bernstein.bsum 1 0 (1499381123511296786702901/211303882501772875000000000:ℝ) cell4_domain4_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain4_0_g]
def cell4_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(731965184631742753900967/105651941250886437500000:ℝ)],
  ![(499793707837098928900967/105651941250886437500000:ℝ)]]
theorem cell4_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 4 true b := by
 have heq : domainBranch cell4 4 true b = Record12518109.Bernstein.bsum 1 0 (1499381123511296786702901/211303882501772875000000000:ℝ) cell4_domain4_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain4_1_g]
def cell4_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(575519575710102623355642359659/211303882501772875000000000000:ℝ)],
  ![(496578775292268434532211109659/211303882501772875000000000000:ℝ)]]
theorem cell4_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 5 false b := by
 have heq : domainBranch cell4 5 false b = Record12518109.Bernstein.bsum 1 0 (1489736325876805303596633328977/422607765003545750000000000000000:ℝ) cell4_domain5_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain5_0_g]
def cell4_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(7438163075504568818221399101271/1267823295010637250000000000000:ℝ)],
  ![(6964518272997563685280811601271/1267823295010637250000000000000:ℝ)]]
theorem cell4_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 5 true b := by
 have heq : domainBranch cell4 5 true b = Record12518109.Bernstein.bsum 1 0 (6964518272997563685280811601271/845215530007091500000000000000000:ℝ) cell4_domain5_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain5_1_g]
def cell4_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(11329246088886328307379542525067259/214916228025081933184562500000000:ℝ)],
  ![(10790349594974602504434749046942259/214916228025081933184562500000000:ℝ)]]
theorem cell4_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 6 false b := by
 have heq : domainBranch cell4 6 false b = Record12518109.Bernstein.bsum 1 0 (32371048784923807513304247140826777/429832456050163866369125000000000000:ℝ) cell4_domain6_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain6_0_g]
def cell4_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(44266778355702568110425221274144739/859664912100327732738250000000000:ℝ)],
  ![(42111192380055664898646047361644739/859664912100327732738250000000000:ℝ)]]
theorem cell4_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 6 true b := by
 have heq : domainBranch cell4 6 true b = Record12518109.Bernstein.bsum 1 0 (126333577140166994695938142084934217/1719329824200655465476500000000000000:ℝ) cell4_domain6_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain6_1_g]
def cell4_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(525287400749308159983302061/33808621200283660000000000:ℝ)],
  ![(707044622220989045133902061/33808621200283660000000000:ℝ)]]
theorem cell4_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 7 false b := by
 have heq : domainBranch cell4 7 false b = Record12518109.Bernstein.bsum 1 0 (1575862202247924479949906183/67617242400567320000000000000:ℝ) cell4_domain7_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain7_0_g]
def cell4_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(525287400749308159983302061/33808621200283660000000000:ℝ)],
  ![(707044622220989045133902061/33808621200283660000000000:ℝ)]]
theorem cell4_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 7 true b := by
 have heq : domainBranch cell4 7 true b = Record12518109.Bernstein.bsum 1 0 (1575862202247924479949906183/67617242400567320000000000000:ℝ) cell4_domain7_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain7_1_g]
def cell4_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(555428420381143270081376462987/21130388250177287500000000000:ℝ)],
  ![(522288708778806333568207712987/21130388250177287500000000000:ℝ)]]
theorem cell4_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 8 false b := by
 have heq : domainBranch cell4 8 false b = Record12518109.Bernstein.bsum 1 0 (1566866126336419000704623138961/42260776500354575000000000000000:ℝ) cell4_domain8_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain8_0_g]
def cell4_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(3485994065579523073626879841253/126782329501063725000000000000:ℝ)],
  ![(3287155795965501454547867341253/126782329501063725000000000000:ℝ)]]
theorem cell4_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell4 8 true b := by
 have heq : domainBranch cell4 8 true b = Record12518109.Bernstein.bsum 1 0 (3287155795965501454547867341253/84521553000709150000000000000000:ℝ) cell4_domain8_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_domain8_1_g]
def cell4_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(28527737879486469719869/12171103632102117600000:ℝ)],
  ![(37814596951272222719869/12171103632102117600000:ℝ)]]
theorem cell4_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell4 0 b := by
 have heq : ordinary cell4 0 b = Record12518109.Bernstein.bsum 1 0 (28527737879486469719869/8114069088068078400000000:ℝ) cell4_ordinary0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordinary0_g]
def cell4_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(10069828525620087593377/4057034544034039200000:ℝ)],
  ![(6974208835024836593377/4057034544034039200000:ℝ)]]
theorem cell4_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell4 1 b := by
 have heq : ordinary cell4 1 b = Record12518109.Bernstein.bsum 1 0 (6974208835024836593377/2704689696022692800000000:ℝ) cell4_ordinary1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordinary1_g]
def cell4_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(4056895896733722772547273/12678232950106372500000:ℝ)],
  ![(3998853027535061816297273/12678232950106372500000:ℝ)]]
theorem cell4_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell4 2 b := by
 have heq : ordinary cell4 2 b = Record12518109.Bernstein.bsum 1 0 (3998853027535061816297273/8452155300070915000000000:ℝ) cell4_ordinary2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordinary2_g]
def cell4_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(374999989/30000000:ℝ)],
  ![(404999989/30000000:ℝ)]]
theorem cell4_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell4 3 b := by
 have heq : ordinary cell4 3 b = Record12518109.Bernstein.bsum 1 0 (374999989/20000000000:ℝ) cell4_ordinary3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordinary3_g]
def cell4_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(7545046281920415334900559/25356465900212745000000:ℝ)],
  ![(7378247611722667932400559/25356465900212745000000:ℝ)]]
theorem cell4_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell4 4 b := by
 have heq : ordinary cell4 4 b = Record12518109.Bernstein.bsum 1 0 (7378247611722667932400559/16904310600141830000000000:ℝ) cell4_ordinary4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordinary4_g]
def cell4_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(9044653567665814183/2744912925108000000000000:ℝ)],
  ![(9044653567665814183/2744912925108000000000000:ℝ)]]
theorem cell4_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell4 5 b := by
 have heq : ordinary cell4 5 b = Record12518109.Bernstein.bsum 1 0 (9044653567665814183/1829941950072000000000000000:ℝ) cell4_ordinary5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordinary5_g]
def cell4_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(28527332176032066315949/12171103632102117600000:ℝ)],
  ![(37814191247817819315949/12171103632102117600000:ℝ)]]
theorem cell4_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 0 false b := by
 have heq : complementBranch cell4 0 false b = Record12518109.Bernstein.bsum 1 0 (28527332176032066315949/8114069088068078400000000:ℝ) cell4_complement0_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement0_0_g]
def cell4_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(230208532251853786713027930743/101379883876018594222400000000:ℝ)],
  ![(307914873238460709348223730743/101379883876018594222400000000:ℝ)]]
theorem cell4_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 0 true b := by
 have heq : complementBranch cell4 0 true b = Record12518109.Bernstein.bsum 1 0 (690625596755561360139083792229/202759767752037188444800000000000:ℝ) cell4_complement0_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement0_1_g]
def cell4_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(8981911722348003148445706451/304277590802552940000000000:ℝ)],
  ![(8642619047421217089092706451/304277590802552940000000000:ℝ)]]
theorem cell4_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 1 false b := by
 have heq : complementBranch cell4 1 false b = Record12518109.Bernstein.bsum 1 0 (8642619047421217089092706451/202851727201701960000000000000:ℝ) cell4_complement1_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement1_0_g]
def cell4_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(223876978146732454882263922790947/7603491290701394566680000000000:ℝ)],
  ![(215424826521411736509767941790947/7603491290701394566680000000000:ℝ)]]
theorem cell4_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 1 true b := by
 have heq : complementBranch cell4 1 true b = Record12518109.Bernstein.bsum 1 0 (215424826521411736509767941790947/5068994193800929711120000000000000:ℝ) cell4_complement1_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement1_1_g]
def cell4_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(732608987554293758495422939/33808621200283660000000000:ℝ)],
  ![(591722478431475829678422939/33808621200283660000000000:ℝ)]]
theorem cell4_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 2 false b := by
 have heq : complementBranch cell4 2 false b = Record12518109.Bernstein.bsum 1 0 (1775167435294427489035268817/67617242400567320000000000000:ℝ) cell4_complement2_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement2_0_g]
def cell4_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(492579828511613633714721822972841/22810473872104183700040000000000:ℝ)],
  ![(397603505918102402657433879972841/22810473872104183700040000000000:ℝ)]]
theorem cell4_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 2 true b := by
 have heq : complementBranch cell4 2 true b = Record12518109.Bernstein.bsum 1 0 (397603505918102402657433879972841/15206982581402789133360000000000000:ℝ) cell4_complement2_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement2_1_g]
def cell4_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(7550502158920823378942431451/304277590802552940000000000:ℝ)],
  ![(7443380960788681144589431451/304277590802552940000000000:ℝ)]]
theorem cell4_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 3 false b := by
 have heq : complementBranch cell4 3 false b = Record12518109.Bernstein.bsum 1 0 (7443380960788681144589431451/202851727201701960000000000000:ℝ) cell4_complement3_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement3_0_g]
def cell4_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(564323885108315406046209254722841/22810473872104183700040000000000:ℝ)],
  ![(556372397161740519913671311722841/22810473872104183700040000000000:ℝ)]]
theorem cell4_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 3 true b := by
 have heq : complementBranch cell4 3 true b = Record12518109.Bernstein.bsum 1 0 (556372397161740519913671311722841/15206982581402789133360000000000000:ℝ) cell4_complement3_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement3_1_g]
def cell4_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(2417316101541967821231356317/101425863600850980000000000:ℝ)],
  ![(2342913789365479772280356317/101425863600850980000000000:ℝ)]]
theorem cell4_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 4 false b := by
 have heq : complementBranch cell4 4 false b = Record12518109.Bernstein.bsum 1 0 (2342913789365479772280356317/67617242400567320000000000000:ℝ) cell4_complement4_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement4_0_g]
def cell4_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(541942496867242439679700511547841/22810473872104183700040000000000:ℝ)],
  ![(525288525455973919054687568547841/22810473872104183700040000000000:ℝ)]]
theorem cell4_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 4 true b := by
 have heq : complementBranch cell4 4 true b = Record12518109.Bernstein.bsum 1 0 (525288525455973919054687568547841/15206982581402789133360000000000000:ℝ) cell4_complement4_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement4_1_g]
def cell4_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(1467889/50000:ℝ)],
  ![(1242991/50000:ℝ)]]
theorem cell4_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 5 false b := by
 have heq : complementBranch cell4 5 false b = Record12518109.Bernstein.bsum 1 0 (3728973/100000000:ℝ) cell4_complement5_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement5_0_g]
def cell4_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(26718312555825588910630849990687/912418954884167348001600000000:ℝ)],
  ![(22617446985218771090332335454687/912418954884167348001600000000:ℝ)]]
theorem cell4_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 5 true b := by
 have heq : complementBranch cell4 5 true b = Record12518109.Bernstein.bsum 1 0 (22617446985218771090332335454687/608279303256111565334400000000000:ℝ) cell4_complement5_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement5_1_g]
def cell4_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(847068071899900244056997/12171103632102117600000:ℝ)],
  ![(782060058397399973056997/12171103632102117600000:ℝ)]]
theorem cell4_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 6 false b := by
 have heq : complementBranch cell4 6 false b = Record12518109.Bernstein.bsum 1 0 (782060058397399973056997/8114069088068078400000000:ℝ) cell4_complement6_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement6_0_g]
def cell4_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(63433022688554200120793274644687/912418954884167348001600000000:ℝ)],
  ![(58562790340029736349326036844687/912418954884167348001600000000:ℝ)]]
theorem cell4_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 6 true b := by
 have heq : complementBranch cell4 6 true b = Record12518109.Bernstein.bsum 1 0 (58562790340029736349326036844687/608279303256111565334400000000000:ℝ) cell4_complement6_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement6_1_g]
def cell4_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(401872550079470837417668817/608555181605105880000000000:ℝ)],
  ![(552908407286613920966668817/608555181605105880000000000:ℝ)]]
theorem cell4_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 7 false b := by
 have heq : complementBranch cell4 7 false b = Record12518109.Bernstein.bsum 1 0 (401872550079470837417668817/405703454403403920000000000000:ℝ) cell4_complement7_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement7_0_g]
def cell4_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(2232634825597568387220324389131/3801745645350697283340000000000:ℝ)],
  ![(3189340963646673855326361389131/3801745645350697283340000000000:ℝ)]]
theorem cell4_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 7 true b := by
 have heq : complementBranch cell4 7 true b = Record12518109.Bernstein.bsum 1 0 (2232634825597568387220324389131/2534497096900464855560000000000000:ℝ) cell4_complement7_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement7_1_g]
def cell4_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(6107420125976764781391468817/608555181605105880000000000:ℝ)],
  ![(8115827797541058464940468817/608555181605105880000000000:ℝ)]]
theorem cell4_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 8 false b := by
 have heq : complementBranch cell4 8 false b = Record12518109.Bernstein.bsum 1 0 (6107420125976764781391468817/405703454403403920000000000000:ℝ) cell4_complement8_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement8_0_g]
def cell4_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(113628424370471839612645945867393/11405236936052091850020000000000:ℝ)],
  ![(151308476643393693986864056867393/11405236936052091850020000000000:ℝ)]]
theorem cell4_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 8 true b := by
 have heq : complementBranch cell4 8 true b = Record12518109.Bernstein.bsum 1 0 (113628424370471839612645945867393/7603491290701394566680000000000000:ℝ) cell4_complement8_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement8_1_g]
def cell4_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(2511269006650362755794972939/202851727201701960000000000:ℝ)],
  ![(3335519215034889866977972939/202851727201701960000000000:ℝ)]]
theorem cell4_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 9 false b := by
 have heq : complementBranch cell4 9 false b = Record12518109.Bernstein.bsum 1 0 (2511269006650362755794972939/135234484801134640000000000000:ℝ) cell4_complement9_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement9_0_g]
def cell4_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(140361054343891623225392189042393/11405236936052091850020000000000:ℝ)],
  ![(186743590081507112092085300042393/11405236936052091850020000000000:ℝ)]]
theorem cell4_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 9 true b := by
 have heq : complementBranch cell4 9 true b = Record12518109.Bernstein.bsum 1 0 (140361054343891623225392189042393/7603491290701394566680000000000000:ℝ) cell4_complement9_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement9_1_g]
def cell4_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(28527332176032066315949/12171103632102117600000:ℝ)],
  ![(37814191247817819315949/12171103632102117600000:ℝ)]]
theorem cell4_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 10 false b := by
 have heq : complementBranch cell4 10 false b = Record12518109.Bernstein.bsum 1 0 (28527332176032066315949/8114069088068078400000000:ℝ) cell4_complement10_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement10_0_g]
def cell4_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(230208532251853786713027930743/101379883876018594222400000000:ℝ)],
  ![(307914873238460709348223730743/101379883876018594222400000000:ℝ)]]
theorem cell4_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 10 true b := by
 have heq : complementBranch cell4 10 true b = Record12518109.Bernstein.bsum 1 0 (690625596755561360139083792229/202759767752037188444800000000000:ℝ) cell4_complement10_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement10_1_g]
def cell4_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(28527670262244069152549/2028517272017019600000:ℝ)],
  ![(37814529334029822152549/2028517272017019600000:ℝ)]]
theorem cell4_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 11 false b := by
 have heq : complementBranch cell4 11 false b = Record12518109.Bernstein.bsum 1 0 (28527670262244069152549/1352344848011346400000000:ℝ) cell4_complement11_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement11_0_g]
def cell4_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(12764928779634597525515748646687/912418954884167348001600000000:ℝ)],
  ![(16945279234391513626222510846687/912418954884167348001600000000:ℝ)]]
theorem cell4_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 11 true b := by
 have heq : complementBranch cell4 11 true b = Record12518109.Bernstein.bsum 1 0 (12764928779634597525515748646687/608279303256111565334400000000000:ℝ) cell4_complement11_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement11_1_g]
def cell4_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(199693759452950884635163/12171103632102117600000:ℝ)],
  ![(264701772955451155635163/12171103632102117600000:ℝ)]]
theorem cell4_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 12 false b := by
 have heq : complementBranch cell4 12 false b = Record12518109.Bernstein.bsum 1 0 (199693759452950884635163/8114069088068078400000000:ℝ) cell4_complement12_0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement12_0_g]
def cell4_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(4967846392502726738178482700229/304139651628055782667200000000:ℝ)],
  ![(6593362769813529024880070100229/304139651628055782667200000000:ℝ)]]
theorem cell4_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell4 12 true b := by
 have heq : complementBranch cell4 12 true b = Record12518109.Bernstein.bsum 1 0 (4967846392502726738178482700229/202759767752037188444800000000000:ℝ) cell4_complement12_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement12_1_g]
theorem cell4_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 0 b := complementReserve_pos_of_branches (cell4_complement0_0 hb hν) (cell4_complement0_1 hb hν)
theorem cell4_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 1 b := complementReserve_pos_of_branches (cell4_complement1_0 hb hν) (cell4_complement1_1 hb hν)
theorem cell4_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 2 b := complementReserve_pos_of_branches (cell4_complement2_0 hb hν) (cell4_complement2_1 hb hν)
theorem cell4_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 3 b := complementReserve_pos_of_branches (cell4_complement3_0 hb hν) (cell4_complement3_1 hb hν)
theorem cell4_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 4 b := complementReserve_pos_of_branches (cell4_complement4_0 hb hν) (cell4_complement4_1 hb hν)
theorem cell4_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 5 b := complementReserve_pos_of_branches (cell4_complement5_0 hb hν) (cell4_complement5_1 hb hν)
theorem cell4_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 6 b := complementReserve_pos_of_branches (cell4_complement6_0 hb hν) (cell4_complement6_1 hb hν)
theorem cell4_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 7 b := complementReserve_pos_of_branches (cell4_complement7_0 hb hν) (cell4_complement7_1 hb hν)
theorem cell4_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 8 b := complementReserve_pos_of_branches (cell4_complement8_0 hb hν) (cell4_complement8_1 hb hν)
theorem cell4_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 9 b := complementReserve_pos_of_branches (cell4_complement9_0 hb hν) (cell4_complement9_1 hb hν)
theorem cell4_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 10 b := complementReserve_pos_of_branches (cell4_complement10_0 hb hν) (cell4_complement10_1 hb hν)
theorem cell4_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 11 b := complementReserve_pos_of_branches (cell4_complement11_0 hb hν) (cell4_complement11_1 hb hν)
theorem cell4_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell4 12 b := complementReserve_pos_of_branches (cell4_complement12_0 hb hν) (cell4_complement12_1 hb hν)
theorem cell4_all_domains {b : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell4 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell4_domain0_0 (ν := (1271/2000:ℝ)) hb (by norm_num)
   | true => exact cell4_domain0_1 (ν := (1271/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell4_domain1_0 (ν := (1271/2000:ℝ)) hb (by norm_num)
   | true => exact cell4_domain1_1 (ν := (1271/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell4_domain2_0 (ν := (1271/2000:ℝ)) hb (by norm_num)
   | true => exact cell4_domain2_1 (ν := (1271/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell4_domain3_0 (ν := (1271/2000:ℝ)) hb (by norm_num)
   | true => exact cell4_domain3_1 (ν := (1271/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell4_domain4_0 (ν := (1271/2000:ℝ)) hb (by norm_num)
   | true => exact cell4_domain4_1 (ν := (1271/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell4_domain5_0 (ν := (1271/2000:ℝ)) hb (by norm_num)
   | true => exact cell4_domain5_1 (ν := (1271/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell4_domain6_0 (ν := (1271/2000:ℝ)) hb (by norm_num)
   | true => exact cell4_domain6_1 (ν := (1271/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell4_domain7_0 (ν := (1271/2000:ℝ)) hb (by norm_num)
   | true => exact cell4_domain7_1 (ν := (1271/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell4_domain8_0 (ν := (1271/2000:ℝ)) hb (by norm_num)
   | true => exact cell4_domain8_1 (ν := (1271/2000:ℝ)) hb (by norm_num)
end
end Record12518109Admission
