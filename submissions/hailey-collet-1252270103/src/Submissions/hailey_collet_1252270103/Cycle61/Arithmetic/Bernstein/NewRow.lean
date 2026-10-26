import Submissions.hailey_collet_1252270103.Cycle61.Arithmetic.Bernstein.Basis

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle61.Arithmetic.Bernstein

/- Exact rational data from input/packet/references/37-endpoint-receipt.json.
Each identity below is proved by polynomial normalization in Lean. -/
noncomputable def newRowPower (δ p : ℝ) : ℝ :=
  (398992013/6000000000) +
  (-847691647955579/20242494000000000)*p^1 +
  (-17049898247/60000000000)*δ^1 +
  (4114686885209510083240019/26061536275200000000000000)*δ^1*p^1 +
  (3411480590366989891919981/78184608825600000000000000)*δ^1*p^2 +
  (1/2)*δ^2 +
  (-17436064332047875310626673/21717946896000000000000000)*δ^2*p^1 +
  (10912403859245306194973327/21717946896000000000000000)*δ^2*p^2 +
  (-8854210915867231307/65153840688000000000)*δ^2*p^3

noncomputable def newRowMinimum : ℝ := 113219985368027151827923/80061039437414400000000000000

theorem newRowMinimum_pos : 0 < newRowMinimum := by
  norm_num [newRowMinimum]

noncomputable def newRowCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![![(398992013/6000000000 : ℝ), (7228901781244843/121454964000000000 : ℝ), (398825633330579/7590935250000000 : ℝ), (368901232355579/8096997600000000 : ℝ)],
    ![(12689027339/960000000000 : ℝ), (83854858317573445783400171/7505722447257600000000000000 : ℝ), (147236547265982936193680627/15011444894515200000000000000 : ℝ), (9133187977861330033088057/1000762992967680000000000000 : ℝ)],
    ![(14519666299/480000000000 : ℝ), (63228906635457526999720171/4415130851328000000000000000 : ℝ), (33892059190790075098856399/6004577957806080000000000000 : ℝ), (5388590977690473810330833/2943420567552000000000000000 : ℝ)]]

theorem newRowCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients0]

theorem newRowIdentity0 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients0
      ((δ-(0))/((3/8)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients0, Fin.sum_univ_succ]
  ring

theorem newRowBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0) (3/8)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity0]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients0_lower

noncomputable def newRowCoefficients1 : Fin 3 → Fin 4 → ℝ :=
  ![![(14519666299/480000000000 : ℝ), (196783545443170737406120171/8830261702656000000000000000 : ℝ), (9687724850443112867269981603/600457795780608000000000000000 : ℝ), (92046191836335911363534399/8006103943741440000000000000 : ℝ)],
    ![(45389637857/960000000000 : ℝ), (607500665376876441361960513/18764306118144000000000000000 : ℝ), (785294788610583773444396881/37528612236288000000000000000 : ℝ), (30856912832153251885678921/2501907482419200000000000000 : ℝ)],
    ![(32309985779/240000000000 : ℝ), (3879322838514060656431641197/37528612236288000000000000000 : ℝ), (11811683044087853620864368493/150114448945152000000000000000 : ℝ), (594201739558868845372390741/10007629929676800000000000000 : ℝ)]]

theorem newRowCoefficients1_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients1]

theorem newRowIdentity1 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients1
      ((δ-(3/8))/((3/4)-(3/8))) ((p-(0))/((1/4)-(0))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients1, Fin.sum_univ_succ]
  ring

theorem newRowBox1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc (0) (1/4)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity1]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients1_lower

noncomputable def newRowCoefficients2 : Fin 3 → Fin 4 → ℝ :=
  ![![(92046191836335911363534399/8006103943741440000000000000 : ℝ), (2755667078183116797381314543/300228897890304000000000000000 : ℝ), (3477222295400734622076400267/480366236624486400000000000000 : ℝ), (1505170357777092654007933297/266870131458048000000000000000 : ℝ)],
    ![(953941564496131586988534731/80061039437414400000000000000 : ℝ), (5168732233528367043025932799/600457795780608000000000000000 : ℝ), (5617752955979740211273821307/960732473248972800000000000000 : ℝ), (112315476785710602646058113/31396486053888000000000000000 : ℝ)],
    ![(3824459128046058998648960431/160122078874828800000000000000 : ℝ), (22509192624934861709563765907/1200915591561216000000000000000 : ℝ), (27649825960539877821121725439/1921464946497945600000000000000 : ℝ), (11465274902524069417042527853/1067480525832192000000000000000 : ℝ)]]

theorem newRowCoefficients2_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients2]

theorem newRowIdentity2 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients2
      ((δ-(3/8))/((9/16)-(3/8))) ((p-(1/4))/((3/8)-(1/4))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients2, Fin.sum_univ_succ]
  ring

theorem newRowBox2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity2]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients2_lower

noncomputable def newRowCoefficients3 : Fin 3 → Fin 4 → ℝ :=
  ![![(1505170357777092654007933297/266870131458048000000000000000 : ℝ), (9706954962983994661760798011/2401831183122432000000000000000 : ℝ), (52242371854887324076625857/18764306118144000000000000000 : ℝ), (5388590977690473810330833/2943420567552000000000000000 : ℝ)],
    ![(983940764182253110599770903/213496105166438400000000000000 : ℝ), (302278600499961560904073789/113027349793996800000000000000 : ℝ), (6941198585211359938584263/6004577957806080000000000000 : ℝ), (274166842124754444743591/40030519718707200000000000000 : ℝ)],
    ![(1004936350202430440520248509/170796884133150720000000000000 : ℝ), (1056581782086278499691990163/307434391439671296000000000000 : ℝ), (8984764817999723429267729/6004577957806080000000000000 : ℝ), (132310733923507208263021/32024415774965760000000000000 : ℝ)]]

theorem newRowCoefficients3_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients3]

theorem newRowIdentity3 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients3
      ((δ-(3/8))/((15/32)-(3/8))) ((p-(3/8))/((1/2)-(3/8))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients3, Fin.sum_univ_succ]
  ring

theorem newRowBox3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity3]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients3_lower

noncomputable def newRowCoefficients4 : Fin 3 → Fin 4 → ℝ :=
  ![![(1004936350202430440520248509/170796884133150720000000000000 : ℝ), (1056581782086278499691990163/307434391439671296000000000000 : ℝ), (8984764817999723429267729/6004577957806080000000000000 : ℝ), (132310733923507208263021/32024415774965760000000000000 : ℝ)],
    ![(3056800222647645981401700739/426992210332876800000000000000 : ℝ), (16137072135158269421561245249/3842929892995891200000000000000 : ℝ), (31065721269825596957609/16914304106496000000000000 : ℝ), (113219985368027151827923/80061039437414400000000000000 : ℝ)],
    ![(11465274902524069417042527853/1067480525832192000000000000000 : ℝ), (68125818442733860401156874159/9607324732489728000000000000000 : ℝ), (38893474882370933855084591/9382153059072000000000000000 : ℝ), (364248617988544810414200349/200152598593536000000000000000 : ℝ)]]

theorem newRowCoefficients4_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients4 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients4]

theorem newRowIdentity4 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients4
      ((δ-(15/32))/((9/16)-(15/32))) ((p-(3/8))/((1/2)-(3/8))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients4, Fin.sum_univ_succ]
  ring

theorem newRowBox4_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity4]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients4_lower

noncomputable def newRowCoefficients5 : Fin 3 → Fin 4 → ℝ :=
  ![![(3824459128046058998648960431/160122078874828800000000000000 : ℝ), (32669883579048561858520657163/2401831183122432000000000000000 : ℝ), (3885618930977845102208226601/600457795780608000000000000000 : ℝ), (364248617988544810414200349/200152598593536000000000000000 : ℝ)],
    ![(28705175635499274116604257/800610394374144000000000000 : ℝ), (6576019528094266872811236733/300228897890304000000000000000 : ℝ), (905902834049852618240202581/75057224472576000000000000000 : ℝ), (136522469254849286935432679/25019074824192000000000000000 : ℝ)],
    ![(594201739558868845372390741/10007629929676800000000000000 : ℝ), (353786420157541867076903161/8830261702656000000000000000 : ℝ), (980665887809239716153133819/37528612236288000000000000000 : ℝ), (204884295667746884961221311/12509537412096000000000000000 : ℝ)]]

theorem newRowCoefficients5_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients5 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients5]

theorem newRowIdentity5 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients5
      ((δ-(9/16))/((3/4)-(9/16))) ((p-(1/4))/((1/2)-(1/4))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients5, Fin.sum_univ_succ]
  ring

theorem newRowBox5_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity5]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients5_lower

end Cycle61.Arithmetic.Bernstein
