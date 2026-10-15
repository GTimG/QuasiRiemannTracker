/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Mathlib.Tactic

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.Basis; sha256 08fce305df1a39de5659de9c76f4958224c35f0891e588b89f79227989d94d7c -/
section
                     

namespace Cycle61.Arithmetic.Bernstein

noncomputable def basis2 (u : ℝ) : Fin 3 → ℝ :=
  ![(1-u)^2, 2*u*(1-u), u^2]

noncomputable def basis3 (v : ℝ) : Fin 4 → ℝ :=
  ![(1-v)^3, 3*v*(1-v)^2, 3*v^2*(1-v), v^3]

noncomputable def tensor (c : Fin 3 → Fin 4 → ℝ) (u v : ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * (basis2 u i * basis3 v j)

theorem basis2_nonneg {u : ℝ} (hu : u ∈ Set.Icc 0 1) (i : Fin 3) :
    0 ≤ basis2 u i := by
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1-u := by linarith [hu.2]
  fin_cases i <;> simp [basis2] <;> positivity

theorem basis3_nonneg {v : ℝ} (hv : v ∈ Set.Icc 0 1) (j : Fin 4) :
    0 ≤ basis3 v j := by
  have hv0 : 0 ≤ v := hv.1
  have h : 0 ≤ 1-v := by linarith [hv.2]
  fin_cases j <;> simp [basis3] <;> positivity

theorem basis2_partition (u : ℝ) : (∑ i, basis2 u i) = 1 := by
  simp [basis2, Fin.sum_univ_succ]
  ring

theorem basis3_partition (v : ℝ) : (∑ j, basis3 v j) = 1 := by
  simp [basis3, Fin.sum_univ_succ]
  ring

theorem tensor_partition (u v : ℝ) :
    (∑ i, ∑ j, basis2 u i * basis3 v j) = 1 := by
  simp_rw [← Finset.mul_sum]
  rw [basis3_partition]
  simp only [mul_one]
  exact basis2_partition u

theorem tensor_lower_bound {c : Fin 3 → Fin 4 → ℝ} {m u v : ℝ}
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hc : ∀ i j, m ≤ c i j) : m ≤ tensor c u v := by
  have hl : (∑ i : Fin 3, ∑ j : Fin 4, m * (basis2 u i * basis3 v j)) ≤
      tensor c u v := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (hc i j)
      (mul_nonneg (basis2_nonneg hu i) (basis3_nonneg hv j))
  simpa only [← Finset.mul_sum, basis2_partition, basis3_partition, mul_one] using hl

theorem tensor_pos {c : Fin 3 → Fin 4 → ℝ} {m u v : ℝ}
    (hm : 0 < m) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hc : ∀ i j, m ≤ c i j) : 0 < tensor c u v :=
  hm.trans_le (tensor_lower_bound hu hv hc)

theorem normalize_mem {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b) :
    (x-a)/(b-a) ∈ Set.Icc 0 1 := by
  have h : 0 < b-a := sub_pos.mpr hab
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt h)
  · apply (div_le_one h).mpr
    linarith [hx.2]

end Cycle61.Arithmetic.Bernstein

end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.Basis -/

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.NewRow; sha256 b1fdfca9dd19b18909579b3183cbbdd15e06b10a436cf63068eafa59ff72591d -/
section
                                         

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

end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.NewRow -/

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.OldHalf; sha256 6b4d80e895bf7389b2dca4661a712bab0b4c5d94d6e2c6fdb140167ed0a48877 -/
section
                                         

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle61.Arithmetic.Bernstein

/- Exact rational data from input/packet/references/37-endpoint-receipt.json.
Each identity below is proved by polynomial normalization in Lean. -/
noncomputable def oldHalfPower (δ p : ℝ) : ℝ :=
  (164704411363/300000000000) +
  (-349928192406836629/1012124700000000000)*p^1 +
  (-633454411363/750000000000)*δ^1 +
  (107120527459913371/843437250000000000)*δ^1*p^1 +
  (2803219410411998803/11382182315001000000)*δ^1*p^2 +
  (1/2)*δ^2 +
  (-499448321803/1686874500000)*δ^2*p^1 +
  (297270303197/1686874500000)*δ^2*p^2 +
  (-407040606394/3794060771667)*δ^2*p^3

noncomputable def oldHalfMinimum : ℝ := 130800958135492294036529/2529373847778000000000000

theorem oldHalfMinimum_pos : 0 < oldHalfMinimum := by
  norm_num [oldHalfMinimum]

noncomputable def oldHalfCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![![(164704411363/300000000000 : ℝ), (2984099866382222693/6072748200000000000 : ℝ), (164635729623461629/379546762500000000 : ℝ), (152282898771236629/404849880000000000 : ℝ)],
    ![(1393724993171/6000000000000 : ℝ), (22177990710916496233/121454964000000000000 : ℝ), (14819387342378102103241/105390576990750000000000 : ℝ), (1613563104743770457725537/15176243086668000000000000 : ℝ)],
    ![(590430879541/3000000000000 : ℝ), (7730958273509144303/60727482000000000000 : ℝ), (463564320853744121541643/5691091157500500000000000 : ℝ), (130800958135492294036529/2529373847778000000000000 : ℝ)]]

theorem oldHalfCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    oldHalfMinimum ≤ oldHalfCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldHalfMinimum, oldHalfCoefficients0]

theorem oldHalfIdentity0 (δ p : ℝ) :
    oldHalfPower δ p = tensor oldHalfCoefficients0
      ((δ-(0))/((3/4)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [oldHalfPower, tensor, basis2, basis3,
    oldHalfCoefficients0, Fin.sum_univ_succ]
  ring

theorem oldHalfBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0) (3/4)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < oldHalfPower δ p := by
  rw [oldHalfIdentity0]
  exact tensor_pos oldHalfMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldHalfCoefficients0_lower

end Cycle61.Arithmetic.Bernstein

end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.OldHalf -/

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.OldJunction; sha256 04f8a9578dc551bc958663a9fbe3d5b86a7bea0e2020f692d01b45807b30a018 -/
section
                                         

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle61.Arithmetic.Bernstein

/- Exact rational data from input/packet/references/37-endpoint-receipt.json.
Each identity below is proved by polynomial normalization in Lean. -/
noncomputable def oldJunctionPower (δ p : ℝ) : ℝ :=
  (408757013/6000000000) +
  (-868438200950579/20242494000000000)*p^1 +
  (-17163958247/60000000000)*δ^1 +
  (2640821256499421/16868745000000000)*δ^1*p^1 +
  (25663691667794939/569109115750050000)*δ^1*p^2 +
  (1/2)*δ^2 +
  (-27011048373269789/33737490000000000)*δ^2*p^1 +
  (423273524161/843437250000)*δ^2*p^2 +
  (-516895955419/3794060771667)*δ^2*p^3

noncomputable def oldJunctionMinimum : ℝ := 8604603547887123299947/38851182301870080000000000

theorem oldJunctionMinimum_pos : 0 < oldJunctionMinimum := by
  norm_num [oldJunctionMinimum]

noncomputable def oldJunctionCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![![(408757013/6000000000 : ℝ), (7405823182159843/121454964000000000 : ℝ), (408586561325579/7590935250000000 : ℝ), (377929785350579/8096997600000000 : ℝ)],
    ![(13909247339/960000000000 : ℝ), (118838654443054991/9716397120000000000 : ℝ), (38889793160822061518389/3642298340800320000000000 : ℝ), (3977553182805064439503/404699815644480000000000 : ℝ)],
    ![(14958686299/480000000000 : ℝ), (116856840235001173/7773117696000000000 : ℝ), (15038245312962418556011/2428198893866880000000000 : ℝ), (10918392631405858550789/4856397787733760000000000 : ℝ)]]

theorem oldJunctionCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients0]

theorem oldJunctionIdentity0 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients0
      ((δ-(0))/((3/8)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients0, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0) (3/8)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity0]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients0_lower

noncomputable def oldJunctionCoefficients1 : Fin 3 → Fin 4 → ℝ :=
  ![![(14958686299/480000000000 : ℝ), (1795488671796564689/77731176960000000000 : ℝ), (49115675540638521038953/2913838672640256000000000 : ℝ), (39293138677755580351759/3237598525155840000000000 : ℝ)],
    ![(45925497857/960000000000 : ℝ), (1276253507106231241/38865588480000000000 : ℝ), (155199239433446784282263/7284596681600640000000000 : ℝ), (61398779641673510755517/4856397787733760000000000 : ℝ)],
    ![(32358405779/240000000000 : ℝ), (2011425107637518993/19432794240000000000 : ℝ), (95637481291570211971867/1214099446933440000000000 : ℝ), (144298542058845795632477/2428198893866880000000000 : ℝ)]]

theorem oldJunctionCoefficients1_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients1]

theorem oldJunctionIdentity1 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients1
      ((δ-(3/8))/((3/4)-(3/8))) ((p-(0))/((1/4)-(0))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients1, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc (0) (1/4)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity1]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients1_lower

noncomputable def oldJunctionCoefficients2 : Fin 3 → Fin 4 → ℝ :=
  ![![(39293138677755580351759/3237598525155840000000000 : ℝ), (569757988893015459107963/58276773452805120000000000 : ℝ), (1775121834879341371169/227643646300020000000000 : ℝ), (7980343197688096351457/1295039410062336000000000 : ℝ)],
    ![(240676975316613762566311/19425591150935040000000000 : ℝ), (117126562745483501730913/12950394100623360000000000 : ℝ), (45514064548767732453973/7284596681600640000000000 : ℝ), (51086421297411940855991/12950394100623360000000000 : ℝ)],
    ![(940668702835343966607253/38851182301870080000000000 : ℝ), (887593620729290225498567/46621418762244096000000000 : ℝ), (106757848392634055129911/7284596681600640000000000 : ℝ), (284359495384251617042941/25900788201246720000000000 : ℝ)]]

theorem oldJunctionCoefficients2_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients2]

theorem oldJunctionIdentity2 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients2
      ((δ-(3/8))/((9/16)-(3/8))) ((p-(1/4))/((3/8)-(1/4))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients2, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity2]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients2_lower

noncomputable def oldJunctionCoefficients3 : Fin 3 → Fin 4 → ℝ :=
  ![![(7980343197688096351457/1295039410062336000000000 : ℝ), (131899849031408640305933/29138386726402560000000000 : ℝ), (62831668520142412764389/19425591150935040000000000 : ℝ), (10918392631405858550789/4856397787733760000000000 : ℝ)],
    ![(130889853274292904370561/25900788201246720000000000 : ℝ), (359464973349382888684001/116553546905610240000000000 : ℝ), (71468022283180197185191/46621418762244096000000000 : ℝ), (6861324963368519479909/19425591150935040000000000 : ℝ)],
    ![(129662408905532261499209/20720630560997376000000000 : ℝ), (352274076289603332964033/93242837524488192000000000 : ℝ), (337057153328849054988251/186485675048976384000000000 : ℝ), (1488483564974944150651/5180157640249344000000000 : ℝ)]]

theorem oldJunctionCoefficients3_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients3]

theorem oldJunctionIdentity3 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients3
      ((δ-(3/8))/((15/32)-(3/8))) ((p-(3/8))/((1/2)-(3/8))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients3, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity3]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients3_lower

noncomputable def oldJunctionCoefficients4 : Fin 3 → Fin 4 → ℝ :=
  ![![(129662408905532261499209/20720630560997376000000000 : ℝ), (352274076289603332964033/93242837524488192000000000 : ℝ), (337057153328849054988251/186485675048976384000000000 : ℝ), (1488483564974944150651/5180157640249344000000000 : ℝ)],
    ![(386532337979075498754923/51801576402493440000000000 : ℝ), (1042440434749250887452163/233107093811220480000000000 : ℝ), (64707036254162886872623/31080945841496064000000000 : ℝ), (8604603547887123299947/38851182301870080000000000 : ℝ)],
    ![(284359495384251617042941/25900788201246720000000000 : ℝ), (851109884176119671307893/116553546905610240000000000 : ℝ), (1813115517454847907379/418504656752640000000000 : ℝ), (7711104829354703708657/3885118230187008000000000 : ℝ)]]

theorem oldJunctionCoefficients4_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients4 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients4]

theorem oldJunctionIdentity4 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients4
      ((δ-(15/32))/((9/16)-(15/32))) ((p-(3/8))/((1/2)-(3/8))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients4, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox4_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity4]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients4_lower

noncomputable def oldJunctionCoefficients5 : Fin 3 → Fin 4 → ℝ :=
  ![![(940668702835343966607253/38851182301870080000000000 : ℝ), (403990498785104806917769/29138386726402560000000000 : ℝ), (778572198341709173150393/116553546905610240000000000 : ℝ), (7711104829354703708657/3885118230187008000000000 : ℝ)],
    ![(38888429306596122446719/1079199508385280000000000 : ℝ), (80240866023806812486987/3642298340800320000000000 : ℝ), (118061556041667246346793/9712795575467520000000000 : ℝ), (26765492223108358082477/4856397787733760000000000 : ℝ)],
    ![(144298542058845795632477/2428198893866880000000000 : ℝ), (4866106076727558366061/121409944693344000000000 : ℝ), (190287780982572467499889/7284596681600640000000000 : ℝ), (2206245482696271453817/134899938548160000000000 : ℝ)]]

theorem oldJunctionCoefficients5_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients5 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients5]

theorem oldJunctionIdentity5 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients5
      ((δ-(9/16))/((3/4)-(9/16))) ((p-(1/4))/((1/2)-(1/4))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients5, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox5_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity5]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients5_lower

end Cycle61.Arithmetic.Bernstein

end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.OldJunction -/
