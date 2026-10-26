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


noncomputable def basis4 (v : ℝ) : Fin 5 → ℝ :=
  ![(1-v)^4, 4*v*(1-v)^3, 6*v^2*(1-v)^2, 4*v^3*(1-v), v^4]

noncomputable def tensor24 (c : Fin 3 → Fin 5 → ℝ) (u v : ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * (basis2 u i * basis4 v j)

theorem basis4_nonneg {v : ℝ} (hv : v ∈ Set.Icc 0 1) (j : Fin 5) :
    0 ≤ basis4 v j := by
  have hv0 : 0 ≤ v := hv.1
  have h : 0 ≤ 1-v := by linarith [hv.2]
  fin_cases j <;> simp [basis4] <;> positivity

theorem basis4_partition (v : ℝ) : (∑ j, basis4 v j) = 1 := by
  simp [basis4, Fin.sum_univ_succ]
  ring

theorem tensor24_lower_bound {c : Fin 3 → Fin 5 → ℝ} {m u v : ℝ}
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hc : ∀ i j, m ≤ c i j) : m ≤ tensor24 c u v := by
  have hl : (∑ i : Fin 3, ∑ j : Fin 5, m * (basis2 u i * basis4 v j)) ≤
      tensor24 c u v := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (hc i j)
      (mul_nonneg (basis2_nonneg hu i) (basis4_nonneg hv j))
  simpa only [← Finset.mul_sum, basis2_partition, basis4_partition, mul_one] using hl

theorem tensor24_pos {c : Fin 3 → Fin 5 → ℝ} {m u v : ℝ}
    (hm : 0 < m) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hc : ∀ i j, m ≤ c i j) : 0 < tensor24 c u v :=
  hm.trans_le (tensor24_lower_bound hu hv hc)

end Cycle61.Arithmetic.Bernstein

end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.Basis -/

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.NewRow; sha256 b1fdfca9dd19b18909579b3183cbbdd15e06b10a436cf63068eafa59ff72591d -/
section
                                         

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle61.Arithmetic.Bernstein

/- Exact rational data regenerated for theta = 437423/500000, h = 15903/20000
(detector-affine; see proofs/detector-affine-c0125154/arithmetic). The new row is certified
off the affine region; the region itself is certified with the new count.
Each identity below is proved by polynomial normalization in Lean. -/
noncomputable def newRowPower (δ p : ℝ) : ℝ :=
  (78461/1200000) +
  (-83346688009/2024168400000)*p^1 +
  (-1693297/6000000)*δ^1 +
  (8242683343087910773/52120986854400000000)*δ^1*p^1 +
  (6693749240675896427/156362960563200000000)*δ^1*p^2 +
  (1/2)*δ^2 +
  (-34969449116800401191/43434155712000000000)*δ^2*p^1 +
  (7291428932931599603/14478051904000000000)*δ^2*p^2 +
  (-35403493694983/260604934272000)*δ^2*p^3

noncomputable def newRowMinimum : ℝ := 299828456749728237287/62545184225280000000000000

theorem newRowMinimum_pos : 0 < newRowMinimum := by
  norm_num [newRowMinimum]

noncomputable def newRowCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![![(78461/1200000 : ℝ), (710744696153/12145010400000 : ℝ), (39212375509/759063150000 : ℝ), (36270088009/809667360000 : ℝ)],
    ![(6218567/2400000000 : ℝ), (597804017057396310791/375271105351680000000000 : ℝ), (347417552496168718789/250180736901120000000000 : ℝ), (98976064218824964877/50036147380224000000000 : ℝ)],
    ![(15524189/400000000 : ℝ), (1604736901256723954890301/93817776337920000000000000 : ℝ), (198798204137653177691501/37527110535168000000000000 : ℝ), (534021796336988742301/20848394741760000000000000 : ℝ)]]

theorem newRowCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients0]

theorem newRowIdentity0 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients0
      ((δ-(0))/((89/200)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients0, Fin.sum_univ_succ]
  ring

theorem newRowBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0) (89/200)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity0]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients0_lower

noncomputable def newRowCoefficients1 : Fin 3 → Fin 4 → ℝ :=
  ![![(55346191/1200000000 : ℝ), (1921273150555760429816429/93817776337920000000000000 : ℝ), (4737182902542079540079/735825696768000000000000 : ℝ), (299828456749728237287/62545184225280000000000000 : ℝ)],
    ![(58392547/800000000 : ℝ), (3939618593424314484421/117272220422400000000000 : ℝ), (2188909085253018152953/187635552675840000000000 : ℝ), (11924902351947078811/11582441523200000000000 : ℝ)],
    ![(3239329/24000000 : ℝ), (2716892250986611121099/37527110535168000000000 : ℝ), (541995451660899644947/15010844214067200000000 : ℝ), (413959658411674684537/25018073690112000000000 : ℝ)]]

theorem newRowCoefficients1_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients1]

theorem newRowIdentity1 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients1
      ((δ-(97/200))/((3/4)-(97/200))) ((p-(0))/((1/2)-(0))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients1, Fin.sum_univ_succ]
  ring

theorem newRowBox1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (97/200) (3/4)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity1]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients1_lower

noncomputable def newRowCoefficients2 : Fin 3 → Fin 4 → ℝ :=
  ![![(15524189/400000000 : ℝ), (18056673939221074044593311/1042419737088000000000000000 : ℝ), (1153873781235611627626996189/208483947417600000000000000000 : ℝ), (759264951193389509678617/4087920537600000000000000000 : ℝ)],
    ![(50479379/1200000000 : ℝ), (19529546125430052356460103/1042419737088000000000000000 : ℝ), (1231490916642825808858149397/208483947417600000000000000000 : ℝ), (1820138442662335304911297/69494649139200000000000000000 : ℝ)],
    ![(55346191/1200000000 : ℝ), (21614787671705383326380719/1042419737088000000000000000 : ℝ), (1400989590777060273990960781/208483947417600000000000000000 : ℝ), (4634684477315630457979827/23164883046400000000000000000 : ℝ)]]

theorem newRowCoefficients2_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients2]

theorem newRowIdentity2 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients2
      ((δ-(89/200))/((97/200)-(89/200))) ((p-(0))/((99/200)-(0))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients2, Fin.sum_univ_succ]
  ring

theorem newRowBox2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200) (97/200)) (hp : p ∈ Set.Icc (0) (99/200)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity2]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients2_lower

end Cycle61.Arithmetic.Bernstein

end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.NewRow -/

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.OldHalf; sha256 6b4d80e895bf7389b2dca4661a712bab0b4c5d94d6e2c6fdb140167ed0a48877 -/
section
                                         

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle61.Arithmetic.Bernstein

/- Exact rational data regenerated for theta = 437423/500000, h = 15903/20000
(detector-affine; see proofs/detector-affine-c0125154/arithmetic). 
Each identity below is proved by polynomial normalization in Lean. -/
noncomputable def oldHalfPower (δ p : ℝ) : ℝ :=
  (659861/1200000) +
  (-700949884609/2024168400000)*p^1 +
  (-2534861/3000000)*δ^1 +
  (214431057611/1686807000000)*δ^1*p^1 +
  (35041390952907641/142265892762450000)*δ^1*p^2 +
  (1/2)*δ^2 +
  (-62468428361/210850875000)*δ^2*p^1 +
  (37119290389/210850875000)*δ^2*p^2 +
  (-101602161556/948439285083)*δ^2*p^3

noncomputable def oldHalfMinimum : ℝ := 197375096529940859/3793757140332000000

theorem oldHalfMinimum_pos : 0 < oldHalfMinimum := by
  norm_num [oldHalfMinimum]

noncomputable def oldHalfCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![![(659861/1200000 : ℝ), (5977399038353/12145010400000 : ℝ), (329778072109/759063150000 : ℝ), (305033284609/809667360000 : ℝ)],
    ![(5592637/24000000 : ℝ), (44513077266673/242900208000000 : ℝ), (3213704797307458013/22762542841992000000 : ℝ), (180091059933602029/1686114284592000000 : ℝ)],
    ![(2369027/12000000 : ℝ), (15523633501649/121450104000000 : ℝ), (207052057914793639/2529171426888000000 : ℝ), (197375096529940859/3793757140332000000 : ℝ)]]

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

/- Exact rational data regenerated for theta = 437423/500000, h = 15903/20000
(detector-affine; see proofs/detector-affine-c0125154/arithmetic). 
Each identity below is proved by polynomial normalization in Lean. -/
noncomputable def oldJunctionPower (δ p : ℝ) : ℝ :=
  (40207/600000) +
  (-42710649683/1012084200000)*p^1 +
  (-1704703/6000000)*δ^1 +
  (132235258927/843403500000)*δ^1*p^1 +
  (6300356762026391/142265892762450000)*δ^1*p^2 +
  (1/2)*δ^2 +
  (-1354315095463/1686807000000)*δ^2*p^1 +
  (106060696639/210850875000)*δ^2*p^2 +
  (-129178724056/948439285083)*δ^2*p^3

noncomputable def oldJunctionMinimum : ℝ := 64445262726137509/323733942641664000000

theorem oldJunctionMinimum_pos : 0 < oldJunctionMinimum := by
  norm_num [oldJunctionMinimum]

noncomputable def oldJunctionCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![![(40207/600000 : ℝ), (364218044611/6072505200000 : ℝ), (20094212183/379531575000 : ℝ), (18586449683/404833680000 : ℝ)],
    ![(1319011/96000000 : ℝ), (5638133649677/485800416000000 : ℝ), (308477854603491913/30350057122656000000 : ℝ), (285718257405934339/30350057122656000000 : ℝ)],
    ![(1477451/48000000 : ℝ), (5724030868879/388640332800000 : ℝ), (1084422730523196031/182100342735936000000 : ℝ), (1858111096725559/899260951782400000 : ℝ)]]

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
  ![![(1477451/48000000 : ℝ), (88432346879363/3886403328000000 : ℝ), (502232841623058077/30350057122656000000 : ℝ), (115204925006209891/9712018279249920000 : ℝ)],
    ![(4590793/96000000 : ℝ), (63806577652747/1943201664000000 : ℝ), (3881860469619740227/182100342735936000000 : ℝ), (307537788945180113/24280045698124800000 : ℝ)],
    ![(3244171/24000000 : ℝ), (100872547538531/971600832000000 : ℝ), (719795392577297977/9105017136796800000 : ℝ), (16099884173729039/269778285534720000 : ℝ)]]

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
  ![![(115204925006209891/9712018279249920000 : ℝ), (4622506642481277209/485600913962496000000 : ℝ), (11008025467321082443/1456802741887488000000 : ℝ), (480431005352895061/80933485660416000000 : ℝ)],
    ![(397033400973803227/32373394264166400000 : ℝ), (26018479054031080889/2913605483774976000000 : ℝ), (3580424308578863191/582721096754995200000 : ℝ), (311678936988850573/80933485660416000000 : ℝ)],
    ![(4704154932082996927/194240365584998400000 : ℝ), (110994868581639707891/5827210967549952000000 : ℝ), (85470587065352050063/5827210967549952000000 : ℝ), (3558962663651489407/323733942641664000000 : ℝ)]]

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
  ![![(480431005352895061/80933485660416000000 : ℝ), (6287490725383139753/1456802741887488000000 : ℝ), (4426450443567946247/1456802741887488000000 : ℝ), (1858111096725559/899260951782400000 : ℝ)],
    ![(396054971170872817/80933485660416000000 : ℝ), (17113743371069204807/5827210967549952000000 : ℝ), (325786427839367683/233088438701998080000 : ℝ), (111351960666014969/485600913962496000000 : ℝ)],
    ![(1594823636194774847/258987154113331200000 : ℝ), (17191415881769165761/4661768774039961600000 : ℝ), (2682044874186915217/1553922924679987200000 : ℝ), (83207941902088493/388480731169996800000 : ℝ)]]

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
  ![![(1594823636194774847/258987154113331200000 : ℝ), (17191415881769165761/4661768774039961600000 : ℝ), (2682044874186915217/1553922924679987200000 : ℝ), (83207941902088493/388480731169996800000 : ℝ)],
    ![(4805678411606891699/647467885283328000000 : ℝ), (51729592666707419191/11654421935099904000000 : ℝ), (4788270344167068821/2330884387019980800000 : ℝ), (64445262726137509/323733942641664000000 : ℝ)],
    ![(3558962663651489407/323733942641664000000 : ℝ), (42652068826101568589/5827210967549952000000 : ℝ), (25357832103138744943/5827210967549952000000 : ℝ), (974011859078184449/485600913962496000000 : ℝ)]]

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
  ![![(4704154932082996927/194240365584998400000 : ℝ), (20216272300197376993/1456802741887488000000 : ℝ), (19513760948669638249/2913605483774976000000 : ℝ), (974011859078184449/485600913962496000000 : ℝ)],
    ![(1756527364580793623/48560091396249600000 : ℝ), (1345023691257700763/60700114245312000000 : ℝ), (8939986463561011451/728401370943744000000 : ℝ), (45478329817602347/8093348566041600000 : ℝ)],
    ![(16099884173729039/269778285534720000 : ℝ), (733893578298824311/18210034273593600000 : ℝ), (1597297113399554251/60700114245312000000 : ℝ), (501383232008976709/30350057122656000000 : ℝ)]]

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
