import Candidate.Uneven.RoundedRowsBase
import Candidate.Uneven.RoundedCoarse2
import Candidate.Uneven.RoundedCover3
import Candidate.Uneven.RoundedCriticalBridge
import Candidate.Uneven.RowInterpolation

/- Original module: Candidate.Uneven.RoundedCoarse1. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem coarse_gap_1_0 {d p : ℝ}
    (hd : (9/16:ℝ) ≤ d ∧ d ≤ (3/4:ℝ))
    (hp : (1/4:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 ≤ gap 1 0 d p := by
  let bx : ℝ := (d-(9/16:ℝ))/(3/16:ℝ)
  let byv : ℝ := (p-(1/4:ℝ))/(1/4:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : gap 1 0 d p =
    (594753749018978610372347584829375133006097469/24277791636511488000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (257505479834702897719434221964216938083768637/6069447909127872000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (505862304335712503086170640265254622349356689/24277791636511488000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (5426372270422836540463310803522176864537961/2427779163651148800000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (222080474785481675437360585095161523084920383/3034723954563936000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (17102239322707480357987285229609803426344017/126446831440164000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (229819136443239777361702116092079026638501667/3034723954563936000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (666711056417127255839230480415281284558623/56198591751184000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (30454599514787976999436186964748416123527607/505787325760656000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (9280764632066758662841744351411889278717859/75868098864098400000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (40558941999612455857900825387473040970655299/505787325760656000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 +
    (12805420878063553925579840058516613166595769/758680988640984000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [gap,base,denominator,numerator,theta,reserve,h,y,ell,
      rowHeight,rowCapacity,planeB,planeLambda,bx,byv]
    norm_num
    ring
  rw [hid]
  positivity

theorem coarse_gap_1_1 {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (9/16:ℝ))
    (hp : (3/8:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 ≤ gap 1 0 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/32:ℝ)
  let byv : ℝ := (p-(3/8:ℝ))/(1/8:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : gap 1 0 d p =
    (81530755885746273760037663879070251772341257/12948155539472793600000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (222964089855987309021699676758726920325449909/19422233309209190400000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (8045918594989126106309296662889406751601049/1438683948830310400000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (3408944331949209069261015157132299435150569/9711116654604595200000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (246773506509357483033196724366579478643362379/16185194424340992000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (675304064321157571186928703847712823619688399/24277791636511488000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (130931021402787045333916015487068281181698437/9711116654604595200000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (3130263321097601492104256722660758078579377/4046298606085248000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (182075141283144255811740685082226606361325693/16185194424340992000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (551134424030730423315994373123260575742481689/24277791636511488000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (668653472448397599300069964370919928285495519/48555583273022976000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 +
    (5426372270422836540463310803522176864537961/2427779163651148800000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [gap,base,denominator,numerator,theta,reserve,h,y,ell,
      rowHeight,rowCapacity,planeB,planeLambda,bx,byv]
    norm_num
    ring
  rw [hid]
  positivity

theorem coarse_gap_1_2 {d p : ℝ}
    (hd : (3/8:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (3/8:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 ≤ gap 1 0 d p := by
  let bx : ℝ := (d-(3/8:ℝ))/(3/32:ℝ)
  let byv : ℝ := (p-(3/8:ℝ))/(1/8:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : gap 1 0 d p =
    (4809095384658032927276777787220945396815361/809259721217049600000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (78836686167087956512658837305367382532588609/6069447909127872000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (111385567186014792578166214747576756983663191/12138895818255744000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (2116250257106218257999674122275652752247199/1011574651521312000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (80440136459686942883495797514385890109171953/8092597212170496000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (219758192479389486960784839972960889003780573/12138895818255744000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (43154390330959679768217497205472850555764943/4855558327302297600000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (3826965848226620434996152808839611470007357/6069447909127872000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (81530755885746273760037663879070251772341257/12948155539472793600000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (222964089855987309021699676758726920325449909/19422233309209190400000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (8045918594989126106309296662889406751601049/1438683948830310400000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 +
    (3408944331949209069261015157132299435150569/9711116654604595200000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [gap,base,denominator,numerator,theta,reserve,h,y,ell,
      rowHeight,rowCapacity,planeB,planeLambda,bx,byv]
    norm_num
    ring
  rw [hid]
  positivity

theorem coarse_gap_1_3 {d p : ℝ}
    (hd : (3/8:ℝ) ≤ d ∧ d ≤ (9/16:ℝ))
    (hp : (1/4:ℝ) ≤ p ∧ p ≤ (3/8:ℝ)) :
    0 ≤ gap 1 0 d p := by
  let bx : ℝ := (d-(3/8:ℝ))/(3/16:ℝ)
  let byv : ℝ := (p-(1/4:ℝ))/(1/8:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : gap 1 0 d p =
    (71887044054507632616139488025710034148747221/6069447909127872000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (115443082362585689128905172668135956049906433/4046298606085248000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (34393151535630881303699040779893790081025659/1517361977281968000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (4809095384658032927276777787220945396815361/809259721217049600000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (5577511090667231833245422764409336549490989/224794367004736000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (660892830192898312187226440752753448379331841/12138895818255744000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (57264455843186487140271252854340450332640433/1517361977281968000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (32349182613106613610728019642176436141018343/4046298606085248000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (594753749018978610372347584829375133006097469/24277791636511488000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (562856633279149484398955928468998630270673391/9711116654604595200000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (271885461879391969747417948154194720377362387/6069447909127872000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 +
    (182075141283144255811740685082226606361325693/16185194424340992000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [gap,base,denominator,numerator,theta,reserve,h,y,ell,
      rowHeight,rowCapacity,planeB,planeLambda,bx,byv]
    norm_num
    ring
  rw [hid]
  positivity

theorem coarse_gap_1_4 {d p : ℝ}
    (hd : (3/8:ℝ) ≤ d ∧ d ≤ (3/4:ℝ))
    (hp : (0/1:ℝ) ≤ p ∧ p ≤ (1/4:ℝ)) :
    0 ≤ gap 1 0 d p := by
  let bx : ℝ := (d-(3/8:ℝ))/(3/8:ℝ)
  let byv : ℝ := (p-(0/1:ℝ))/(1/4:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : gap 1 0 d p =
    (368361378040654752907027717883/12000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (220508857389888486190572288852037627019/3238519104000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (10021804980093720871951329140899414639633523/202314930304262400000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (71887044054507632616139488025710034148747221/6069447909127872000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (1155273259265339031218378047969/12000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (161037542470011133190540122941874901011/809629776000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (98447053859106849283217854192933223489493199/758680988640984000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (39352877696753813440743463306671026343754741/1517361977281968000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (815330940612342139155675165043/6000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (253759311837924772296492668265127560203/809629776000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (181283749312424206366508239168616852324569873/758680988640984000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 +
    (30454599514787976999436186964748416123527607/505787325760656000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [gap,base,denominator,numerator,theta,reserve,h,y,ell,
      rowHeight,rowCapacity,planeB,planeLambda,bx,byv]
    norm_num
    ring
  rw [hid]
  positivity

theorem coarse_gap_1_5 {d p : ℝ}
    (hd : (0/1:ℝ) ≤ d ∧ d ≤ (3/8:ℝ))
    (hp : (0/1:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 ≤ gap 1 0 d p := by
  let bx : ℝ := (d-(0/1:ℝ))/(3/8:ℝ)
  let byv : ℝ := (p-(0/1:ℝ))/(1/2:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : gap 1 0 d p =
    (9919510935707815343783813821/150000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (898522126484053784045177368377450553/5060186100000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (49572051615923371925670200919666209/316261631250000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (45852235015032941171751270736791209/1012037220000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (318172252897279980409732823563/12000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (13635549344773667653240059570008912261/202407444000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (7492066016664640261229413040238576151348799/126446831440164000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (6979197002091663358749739756323794953425157/379340494320492000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (368361378040654752907027717883/12000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (14278137478967034589169237764867076983/323851910400000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (27123405122073449806087506723067066336494409/1517361977281968000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 +
    (2116250257106218257999674122275652752247199/1011574651521312000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [gap,base,denominator,numerator,theta,reserve,h,y,ell,
      rowHeight,rowCapacity,planeB,planeLambda,bx,byv]
    norm_num
    ring
  rw [hid]
  positivity

theorem coarse_row_1 {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    ∃ i : ℕ, i ≤ 7 ∧ available i d p ∧ row 1 i d p ≤ theta-reserve := by
  refine ⟨0,by norm_num,Or.inl rfl,row_bound_of_gap (denominator_pos (by norm_num) hd hp) ?_⟩
  by_cases h0 : d ≤ (3/8:ℝ)
  · apply coarse_gap_1_5
    all_goals constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,h0]
  · by_cases h1 : p ≤ (1/4:ℝ)
    · apply coarse_gap_1_4
      all_goals constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,h0,h1]
    · by_cases h2 : d ≤ (9/16:ℝ)
      · by_cases h3 : p ≤ (3/8:ℝ)
        · apply coarse_gap_1_3
          all_goals constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,h0,h1,h2,h3]
        · by_cases h4 : d ≤ (15/32:ℝ)
          · apply coarse_gap_1_2
            all_goals constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,h0,h1,h2,h3,h4]
          · apply coarse_gap_1_1
            all_goals constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,h0,h1,h2,h3,h4]
      · apply coarse_gap_1_0
        all_goals constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,h0,h1,h2]

end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.RoundedCoarse0. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem coarse_gap_0_0 {d p : ℝ}
    (hd : (0/1:ℝ) ≤ d ∧ d ≤ (3/4:ℝ))
    (hp : (0/1:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 ≤ gap 0 0 d p := by
  let bx : ℝ := (d-(0/1:ℝ))/(3/4:ℝ)
  let byv : ℝ := (p-(0/1:ℝ))/(1/2:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : gap 0 0 d p =
    (10279286742492942048154593122771/7500000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (931111084252768734095911308949504922903/253009305000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (51370005666249760886767160154936355759/15813081562500000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (47515273137814907618709187733897230759/50601861000000000000000000000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (104786937122380014818628083087107/75000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (8250792707932433379968307985019999920243/2530093050000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (1464633592063664184578595236152463017991863147/592719522375768750000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (2878891426209023706136736115548360769346111201/4741756179006150000000000000000000000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (23087819697450594337082151859397/75000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (1542409457456153820890444895524950691213/2530093050000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (235760432644742546551276394076780286167072407/592719522375768750000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 +
    (405623944292199661597556232314892882027884351/4741756179006150000000000000000000000000000000:ℝ)*bx^2*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [gap,base,denominator,numerator,theta,reserve,h,y,ell,
      rowHeight,rowCapacity,planeB,planeLambda,bx,byv]
    norm_num
    ring
  rw [hid]
  positivity

theorem coarse_row_0 {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    ∃ i : ℕ, i ≤ 7 ∧ available i d p ∧ row 0 i d p ≤ theta-reserve := by
  refine ⟨0,by norm_num,Or.inl rfl,row_bound_of_gap (denominator_pos (by norm_num) hd hp) ?_⟩
  apply coarse_gap_0_0
  all_goals constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2]

end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.RoundedAvailability. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem critical_plane_available {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) : available 7 d p := by
  norm_num [available]
  rcases le_total d (237/512) with h₁ | h₁
  · exact Or.inl ⟨hd.1,h₁,hp⟩
  · right
    rcases le_total d (15/32) with h₂ | h₂
    · exact Or.inl ⟨h₁,h₂,hp⟩
    · right
      rcases le_total d (123/256) with h₃ | h₃
      · exact Or.inl ⟨h₂,h₃,hp⟩
      · exact Or.inr ⟨h₃,hd.2,hp⟩

end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.RoundedAllRows. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Complete numerical row cover. Analytic source transfer is separate. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem full_rows {r : ℕ} (hr : r ≤ 3) {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    ∃ i : ℕ, i ≤ 7 ∧ available i d p ∧
      row r i d p ≤ theta-1/20000000000000 := by
  have hreserve : (1/20000000000000:ℝ) ≤ reserve := by norm_num [reserve]
  interval_cases r
  · obtain ⟨i,hi,ha,hb⟩ := coarse_row_0 hd hp
    exact ⟨i,hi,ha,by linarith only [hb,hreserve]⟩
  · obtain ⟨i,hi,ha,hb⟩ := coarse_row_1 hd hp
    exact ⟨i,hi,ha,by linarith only [hb,hreserve]⟩
  · obtain ⟨i,hi,ha,hb⟩ := coarse_row_2 hd hp
    exact ⟨i,hi,ha,by linarith only [hb,hreserve]⟩
  · by_cases hc : (117/256:ℝ) ≤ d ∧ d ≤ 63/128 ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2
    · exact ⟨7,by norm_num,critical_plane_available ⟨hc.1,hc.2.1⟩ hc.2.2,
        upper_row_critical_margin ⟨hc.1,hc.2.1⟩ hc.2.2⟩
    · obtain ⟨i,hi,ha,hb⟩ := complement_row_3 hd hp hc
      exact ⟨i,hi,ha,by linarith only [hb,hreserve]⟩

end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.RoundedRowIntervals. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Full numerical row intervals, conditional only on the stated count bounds. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

def rowConstant (d p : ℝ) : ℝ :=
  (1+d)/2+13*h/75-y/2-ell/2+ell*d*p

def scalarRow (z cap count d p : ℝ) : ℝ :=
  rowConstant d p-9*z/100-d*p*cap/2+3*z*count/4

def oldCapacity (z : ℝ) : ℝ := min z (2*y-z)/(6*frozen_kappa)
def newCapacity (z : ℝ) : ℝ :=
  min ((399999/10000000)*z)
    ((2*y-(2-Critical.physicalB)*z)/Critical.physicalLambda)

def CountBounds (count d p : ℝ) : Prop :=
  ∀ i : ℕ, i ≤ 7 → available i d p → count ≤ numerator i d p/denominator i d p

theorem scalar_row_eq (r i : ℕ) (d p : ℝ) :
    scalarRow (rowHeight r) (rowCapacity r)
      (numerator i d p/denominator i d p) d p = row r i d p := by
  unfold scalarRow rowConstant row base
  ring

theorem scalar_row_mono {z cap count count' d p : ℝ}
    (hz : 0 ≤ z) (hc : count ≤ count') :
    scalarRow z cap count d p ≤ scalarRow z cap count' d p := by
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3*z/4 by positivity)
  unfold scalarRow
  nlinarith only [hh]

theorem scalar_endpoints {r : ℕ} (hr : r ≤ 3) {d p count : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hc : CountBounds count d p) :
    scalarRow (rowHeight r) (rowCapacity r) count d p ≤ theta-1/20000000000000 := by
  obtain ⟨i,hi,ha,hb⟩ := full_rows hr hd hp
  have hz : 0 ≤ rowHeight r := by interval_cases r <;> norm_num [rowHeight]
  have hm := scalar_row_mono (cap:=rowCapacity r) (d:=d) (p:=p) hz (hc i hi ha)
  rw [scalar_row_eq] at hm
  exact hm.trans hb

theorem old_row_formula (z count d p : ℝ) :
    scalarRow z (oldCapacity z) count d p =
      rowConstant d p+(-9/100+3*count/4)*z-
        (d*p/(12*frozen_kappa))*min (0+1*z) (2*y+(-1)*z) := by
  unfold scalarRow oldCapacity
  norm_num [frozen_kappa]
  ring

theorem new_row_formula (z count d p : ℝ) :
    scalarRow z (newCapacity z) count d p =
      rowConstant d p+(-9/100+3*count/4)*z-
        (d*p/2)*min (0+(399999/10000000)*z)
          (2*y/Critical.physicalLambda+(-(2-Critical.physicalB)/Critical.physicalLambda)*z) := by
  have he : (2*y-(2-Critical.physicalB)*z)/Critical.physicalLambda =
      2*y/Critical.physicalLambda+(-(2-Critical.physicalB)/Critical.physicalLambda)*z := by ring
  unfold scalarRow newCapacity
  rw [he]
  simp only [zero_add]
  ring

theorem old_row_interval {z count d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 0 ≤ z ∧ z ≤ rowHeight 1)
    (hc : CountBounds count d p) :
    scalarRow z (oldCapacity z) count d p ≤ theta-1/20000000000000 := by
  have h0 := scalar_endpoints (r:=0) (by norm_num) hd hp hc
  have h1 := scalar_endpoints (r:=1) (by norm_num) hd hp hc
  have he0 : rowCapacity 0=oldCapacity (rowHeight 0) := by
    simpa only [actualCapacity,oldCapacity,show (0:ℕ) ≤ 1 by norm_num,if_pos] using
      row_capacity_eq_actual (r:=0) (by norm_num)
  have he1 : rowCapacity 1=oldCapacity (rowHeight 1) := by
    simpa only [actualCapacity,oldCapacity,show (1:ℕ) ≤ 1 by norm_num,if_pos] using
      row_capacity_eq_actual (r:=1) (by norm_num)
  rw [he0,old_row_formula] at h0
  rw [he1,old_row_formula] at h1
  rw [old_row_formula]
  apply RowInterpolation.min_capacity_between _ _ _ _ _ _ _ _ _ _ _ _ hz h0 h1
  exact div_nonneg (mul_nonneg hd.1 hp.1) (by norm_num [frozen_kappa])

theorem new_row_interval {z count d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3)
    (hc : CountBounds count d p) :
    scalarRow z (newCapacity z) count d p ≤ theta-1/20000000000000 := by
  have h0 := scalar_endpoints (r:=2) (by norm_num) hd hp hc
  have h1 := scalar_endpoints (r:=3) (by norm_num) hd hp hc
  have he0 : rowCapacity 2=newCapacity (rowHeight 2) := by
    simpa only [actualCapacity,newCapacity,show ¬ (2:ℕ) ≤ 1 by norm_num,ite_false] using
      row_capacity_eq_actual (r:=2) (by norm_num)
  have he1 : rowCapacity 3=newCapacity (rowHeight 3) := by
    simpa only [actualCapacity,newCapacity,show ¬ (3:ℕ) ≤ 1 by norm_num,ite_false] using
      row_capacity_eq_actual (r:=3) (by norm_num)
  rw [he0,new_row_formula] at h0
  rw [he1,new_row_formula] at h1
  rw [new_row_formula]
  apply RowInterpolation.min_capacity_between _ _ _ _ _ _ _ _ _ _ _ _ hz h0 h1
  exact div_nonneg (mul_nonneg hd.1 hp.1) (by norm_num)

end Sil.Uneven.RoundedRows
end
