import Candidate.Cycle63.Arithmetic.Bernstein.Basis

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Cycle63.Arithmetic.Bernstein
noncomputable section
open Cycle63.Arithmetic.Bernstein

def newRow (δ p : ℝ) : ℝ :=
    (783851/12000000) +
    (-16653445162127/404844372000000)*p^1 +
    (-33837749/120000000)*δ^1 +
    (8261100569671091319883/52122363413760000000000)*δ^1*p^1 +
    (6646600597758145688117/156367090241280000000000)*δ^1*p^2 +
    (1/2)*δ^2 +
    (-34989928859354377543961/43435302844800000000000)*δ^2*p^1 +
    (7291747907146770632013/14478434281600000000000)*δ^2*p^2 +
    (-1768439291215721/13030590853440000)*δ^2*p^3

def newRow_coeff0 : Fin 3 → Fin 4 → ℝ := ![
    ![(783851/12000000), (142015387756159/2429066232000000), (7835121412127/151816639500000), (7247233162127/161937748800000)],
    ![(23902913/1920000000), (158315726281344144630947/15011240663162880000000000), (279439811508604530724139/30022481326325760000000000), (17479198149853013950049/2001498755088384000000000)],
    ![(28694833/960000000), (124152067093844821526947/8830141566566400000000000), (65567050293787330248743/12008992530530304000000000), (10032452899184893733081/5886761044377600000000000)]]

theorem newRow_lower0 (i : Fin 3) (j : Fin 4) :
    (817654434434158964083/10247673626052526080000000000) ≤ newRow_coeff0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRow_coeff0]

theorem newRow_identity0 (δ p : ℝ) :
    newRow δ p = tensor newRow_coeff0
      ((δ-0)/((3/8)-0)) ((p-0)/((1/2)-0)) := by
  norm_num [newRow, tensor, basis2, basis3, newRow_coeff0, Fin.sum_univ_succ]
  ring

theorem newRow_box0 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < newRow δ p := by
  rw [newRow_identity0]
  exact tensor_pos (by norm_num : (0:ℝ)<(817654434434158964083/10247673626052526080000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower0

def newRow_coeff1 : Fin 3 → Fin 4 → ℝ := ![
    ![(28694833/960000000), (124152067093844821526947/8830141566566400000000000), (65567050293787330248743/12008992530530304000000000), (10032452899184893733081/5886761044377600000000000)],
    ![(492604081/15360000000), (17412109002544816247313421/1200899253053030400000000000), (2391637640203220799745157/480359701221212160000000000), (661005386082638043658943/800599502035353600000000000)],
    ![(271482917/7680000000), (151236889396292589554635559/9607194024424243200000000000), (19593689143955316504191911/3842877609769697280000000000), (2562083445773778083408437/6404796016282828800000000000)]]

theorem newRow_lower1 (i : Fin 3) (j : Fin 4) :
    (817654434434158964083/10247673626052526080000000000) ≤ newRow_coeff1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRow_coeff1]

theorem newRow_identity1 (δ p : ℝ) :
    newRow δ p = tensor newRow_coeff1
      ((δ-(3/8))/((27/64)-(3/8))) ((p-0)/((1/2)-0)) := by
  norm_num [newRow, tensor, basis2, basis3, newRow_coeff1, Fin.sum_univ_succ]
  ring

theorem newRow_box1 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < newRow δ p := by
  rw [newRow_identity1]
  exact tensor_pos (by norm_num : (0:ℝ)<(817654434434158964083/10247673626052526080000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower1

def newRow_coeff2 : Fin 3 → Fin 4 → ℝ := ![
    ![(271482917/7680000000), (151236889396292589554635559/9607194024424243200000000000), (19593689143955316504191911/3842877609769697280000000000), (2562083445773778083408437/6404796016282828800000000000)],
    ![(1136293421/30720000000), (314413796168519238685399309/19214388048848486400000000000), (39647966310240183114614477/7685755219539394560000000000), (2398207248660229900953767/12809592032565657600000000000)],
    ![(597546337/15360000000), (660428221442585291941994159/38428776097696972800000000000), (82526051659855195829557423/15371510439078789120000000000), (2245801234310541036638797/25619184065131315200000000000)]]

theorem newRow_lower2 (i : Fin 3) (j : Fin 4) :
    (817654434434158964083/10247673626052526080000000000) ≤ newRow_coeff2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRow_coeff2]

theorem newRow_identity2 (δ p : ℝ) :
    newRow δ p = tensor newRow_coeff2
      ((δ-(27/64))/((57/128)-(27/64))) ((p-0)/((1/2)-0)) := by
  norm_num [newRow, tensor, basis2, basis3, newRow_coeff2, Fin.sum_univ_succ]
  ring

theorem newRow_box2 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < newRow δ p := by
  rw [newRow_identity2]
  exact tensor_pos (by norm_num : (0:ℝ)<(817654434434158964083/10247673626052526080000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower2

def newRow_coeff3 : Fin 3 → Fin 4 → ℝ := ![
    ![(597546337/15360000000), (660428221442585291941994159/38428776097696972800000000000), (82526051659855195829557423/15371510439078789120000000000), (2245801234310541036638797/25619184065131315200000000000)],
    ![(2448984601/61440000000), (1352457071990717398455183859/76857552195393945600000000000), (33656444471817044251888663/6148604175631515648000000000), (1940989205611163308008857/51238368130262630400000000000)],
    ![(628000651/15360000000), (2775835996546207121471697959/153715104390787891200000000000), (345333625791635831107410727/61486041756315156480000000000), (1682057907967222851937717/102476736260525260800000000000)]]

theorem newRow_lower3 (i : Fin 3) (j : Fin 4) :
    (817654434434158964083/10247673626052526080000000000) ≤ newRow_coeff3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRow_coeff3]

theorem newRow_identity3 (δ p : ℝ) :
    newRow δ p = tensor newRow_coeff3
      ((δ-(57/128))/((117/256)-(57/128))) ((p-0)/((1/2)-0)) := by
  norm_num [newRow, tensor, basis2, basis3, newRow_coeff3, Fin.sum_univ_succ]
  ring

theorem newRow_box3 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < newRow δ p := by
  rw [newRow_identity3]
  exact tensor_pos (by norm_num : (0:ℝ)<(817654434434158964083/10247673626052526080000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower3

def newRow_coeff4 : Fin 3 → Fin 4 → ℝ := ![
    ![(628000651/15360000000), (2775835996546207121471697959/153715104390787891200000000000), (345333625791635831107410727/61486041756315156480000000000), (1682057907967222851937717/102476736260525260800000000000)],
    ![(5087023211/122880000000), (5622593845657186567504726159/307430208781575782400000000000), (699436432656737050803345551/122972083512630312960000000000), (1164195312679341939795437/204953472521050521600000000000)],
    ![(5152150589/122880000000), (11394751990797596479551051959/614860417563151564800000000000), (283744034091024121634321291/49188833405052125184000000000), (829855641613210117888357/409906945042101043200000000000)]]

theorem newRow_lower4 (i : Fin 3) (j : Fin 4) :
    (817654434434158964083/10247673626052526080000000000) ≤ newRow_coeff4 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRow_coeff4]

theorem newRow_identity4 (δ p : ℝ) :
    newRow δ p = tensor newRow_coeff4
      ((δ-(117/256))/((237/512)-(117/256))) ((p-0)/((1/2)-0)) := by
  norm_num [newRow, tensor, basis2, basis3, newRow_coeff4, Fin.sum_univ_succ]
  ring

theorem newRow_box4 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < newRow δ p := by
  rw [newRow_identity4]
  exact tensor_pos (by norm_num : (0:ℝ)<(817654434434158964083/10247673626052526080000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower4

def newRow_coeff5 : Fin 3 → Fin 4 → ℝ := ![
    ![(5152150589/122880000000), (11394751990797596479551051959/614860417563151564800000000000), (283744034091024121634321291/49188833405052125184000000000), (829855641613210117888357/409906945042101043200000000000)],
    ![(2592357139/61440000000), (22939068281078416303643703559/1229720835126303129600000000000), (2857287646051887722908128263/491888334050521251840000000000), (161176299480946474074197/819813890084202086400000000000)],
    ![(20871221243/491520000000), (46184985755476957991789545559/2459441670252606259200000000000), (5756578845381784188333954391/983776668101042503680000000000), (226588654235679191200837/1639627780168404172800000000000)]]

theorem newRow_lower5 (i : Fin 3) (j : Fin 4) :
    (817654434434158964083/10247673626052526080000000000) ≤ newRow_coeff5 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRow_coeff5]

theorem newRow_identity5 (δ p : ℝ) :
    newRow δ p = tensor newRow_coeff5
      ((δ-(237/512))/((477/1024)-(237/512))) ((p-0)/((1/2)-0)) := by
  norm_num [newRow, tensor, basis2, basis3, newRow_coeff5, Fin.sum_univ_succ]
  ring

theorem newRow_box5 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < newRow δ p := by
  rw [newRow_identity5]
  exact tensor_pos (by norm_num : (0:ℝ)<(817654434434158964083/10247673626052526080000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower5

def newRow_coeff6 : Fin 3 → Fin 4 → ℝ := ![
    ![(20871221243/491520000000), (46184985755476957991789545559/2459441670252606259200000000000), (5756578845381784188333954391/983776668101042503680000000000), (226588654235679191200837/1639627780168404172800000000000)],
    ![(10501792687/245760000000), (11622958737199270844072921/614860417563151564800000000), (181205699958118529089114133/30743020878157578240000000000), (817654434434158964083/10247673626052526080000000000)],
    ![(33028217/768000000), (1828375185018394041258311/96071940244242432000000000), (1141190409166507305226019/192143880488484864000000000), (114701827638593181397/64047960162828288000000000)]]

theorem newRow_lower6 (i : Fin 3) (j : Fin 4) :
    (817654434434158964083/10247673626052526080000000000) ≤ newRow_coeff6 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRow_coeff6]

theorem newRow_identity6 (δ p : ℝ) :
    newRow δ p = tensor newRow_coeff6
      ((δ-(477/1024))/((15/32)-(477/1024))) ((p-0)/((1/2)-0)) := by
  norm_num [newRow, tensor, basis2, basis3, newRow_coeff6, Fin.sum_univ_succ]
  ring

theorem newRow_box6 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < newRow δ p := by
  rw [newRow_identity6]
  exact tensor_pos (by norm_num : (0:ℝ)<(817654434434158964083/10247673626052526080000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower6

def newRow_coeff7 : Fin 3 → Fin 4 → ℝ := ![
    ![(33028217/768000000), (1828375185018394041258311/96071940244242432000000000), (1141190409166507305226019/192143880488484864000000000), (114701827638593181397/64047960162828288000000000)],
    ![(397518923/7680000000), (1110793709805324570579829/48035970122121216000000000), (49934630664473072346331/6765629594664960000000000), (9054073562966857983211/160119900407070720000000000)],
    ![(124626419/1920000000), (18272646427187825361366071/600449626526515200000000000), (2696106514398386352023767/240179850610606080000000000), (769879987083276524146693/400299751017676800000000000)]]

theorem newRow_lower7 (i : Fin 3) (j : Fin 4) :
    (817654434434158964083/10247673626052526080000000000) ≤ newRow_coeff7 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRow_coeff7]

theorem newRow_identity7 (δ p : ℝ) :
    newRow δ p = tensor newRow_coeff7
      ((δ-(15/32))/((9/16)-(15/32))) ((p-0)/((1/2)-0)) := by
  norm_num [newRow, tensor, basis2, basis3, newRow_coeff7, Fin.sum_univ_succ]
  ring

theorem newRow_box7 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < newRow δ p := by
  rw [newRow_identity7]
  exact tensor_pos (by norm_num : (0:ℝ)<(817654434434158964083/10247673626052526080000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower7

def newRow_coeff8 : Fin 3 → Fin 4 → ℝ := ![
    ![(124626419/1920000000), (18272646427187825361366071/600449626526515200000000000), (2696106514398386352023767/240179850610606080000000000), (769879987083276524146693/400299751017676800000000000)],
    ![(350239591/3840000000), (3381012067053795227450311/75056203315814400000000000), (22714803830087854597409/1200899253053030400000000), (283046199179374410315503/50037468877209600000000000)],
    ![(64840793/480000000), (2721508812459474606048629/37528101657907200000000000), (543672375772030304675437/15011240663162880000000000), (416260326409465487959927/25018734438604800000000000)]]

theorem newRow_lower8 (i : Fin 3) (j : Fin 4) :
    (817654434434158964083/10247673626052526080000000000) ≤ newRow_coeff8 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRow_coeff8]

theorem newRow_identity8 (δ p : ℝ) :
    newRow δ p = tensor newRow_coeff8
      ((δ-(9/16))/((3/4)-(9/16))) ((p-0)/((1/2)-0)) := by
  norm_num [newRow, tensor, basis2, basis3, newRow_coeff8, Fin.sum_univ_succ]
  ring

theorem newRow_box8 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < newRow δ p := by
  rw [newRow_identity8]
  exact tensor_pos (by norm_num : (0:ℝ)<(817654434434158964083/10247673626052526080000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower8

theorem newRow_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : 0 < newRow δ p := by
  rcases hδ with ⟨hd0,hd1⟩
  rcases hp with ⟨hp0,hp1⟩
  rcases le_total δ (3/8) with h0 | h0
  · exact newRow_box0 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  · rcases le_total δ (9/16) with h1 | h1
    · rcases le_total δ (15/32) with h2 | h2
      · rcases le_total δ (27/64) with h3 | h3
        · exact newRow_box1 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        · rcases le_total δ (57/128) with h4 | h4
          · exact newRow_box2 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
          · rcases le_total δ (117/256) with h5 | h5
            · exact newRow_box3 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
            · rcases le_total δ (237/512) with h6 | h6
              · exact newRow_box4 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
              · rcases le_total δ (477/1024) with h7 | h7
                · exact newRow_box5 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
                · exact newRow_box6 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      · exact newRow_box7 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    · exact newRow_box8 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩

#print axioms newRow_pos

def oldJunction (δ p : ℝ) : ℝ :=
    (396727/6000000) +
    (-8428733699179/202422186000000)*p^1 +
    (-33951161/120000000)*δ^1 +
    (13242130496233/84342577500000)*δ^1*p^1 +
    (49800670236453646267/1138187260694961000000)*δ^1*p^2 +
    (1/2)*δ^2 +
    (-542575071034093/674740620000000)*δ^2*p^1 +
    (42479278811671/84342577500000)*δ^2*p^2 +
    (-51666141496684/379395753564987)*δ^2*p^3

def oldJunction_coeff0 : Fin 3 → Fin 4 → ℝ := ![
    ![(396727/6000000), (71877612886043/1214533116000000), (3965554949179/75908319750000), (3668009699179/80968874400000)],
    ![(25099157/1920000000), (2145149117208737/194325298560000000), (2352643059271116655559/242813282281591680000000), (2190882342778790145347/242813282281591680000000)],
    ![(29122837/960000000), (2232796798536373/155460238848000000), (1648661039916493986709/291375938737910016000000), (197444059151634982171/107917014347374080000000)]]

theorem oldJunction_lower0 (i : Fin 3) (j : Fin 4) :
    (121453290708413616307/3885012516505466880000000) ≤ oldJunction_coeff0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunction_coeff0]

theorem oldJunction_identity0 (δ p : ℝ) :
    oldJunction δ p = tensor oldJunction_coeff0
      ((δ-0)/((3/8)-0)) ((p-0)/((1/2)-0)) := by
  norm_num [oldJunction, tensor, basis2, basis3, oldJunction_coeff0, Fin.sum_univ_succ]
  ring

theorem oldJunction_box0 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < oldJunction δ p := by
  rw [oldJunction_identity0]
  exact tensor_pos (by norm_num : (0:ℝ)<(121453290708413616307/3885012516505466880000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) oldJunction_lower0

def oldJunction_coeff1 : Fin 3 → Fin 4 → ℝ := ![
    ![(29122837/960000000), (2232796798536373/155460238848000000), (1648661039916493986709/291375938737910016000000), (197444059151634982171/107917014347374080000000)],
    ![(266129213/7680000000), (47239323494574377/3109204776960000000), (27100667642285649734371/5827518774758200320000000), (121453290708413616307/3885012516505466880000000)],
    ![(33302573/768000000), (47859061475152933/2487363821568000000), (9402229594024060151827/1554005006602186752000000), (157764412357882193959/3108010013204373504000000)]]

theorem oldJunction_lower1 (i : Fin 3) (j : Fin 4) :
    (121453290708413616307/3885012516505466880000000) ≤ oldJunction_coeff1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunction_coeff1]

theorem oldJunction_identity1 (δ p : ℝ) :
    oldJunction δ p = tensor oldJunction_coeff1
      ((δ-(3/8))/((15/32)-(3/8))) ((p-0)/((1/2)-0)) := by
  norm_num [oldJunction, tensor, basis2, basis3, oldJunction_coeff1, Fin.sum_univ_succ]
  ring

theorem oldJunction_box1 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < oldJunction δ p := by
  rw [oldJunction_identity1]
  exact tensor_pos (by norm_num : (0:ℝ)<(121453290708413616307/3885012516505466880000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) oldJunction_lower1

def oldJunction_coeff2 : Fin 3 → Fin 4 → ℝ := ![
    ![(33302573/768000000), (47859061475152933/2487363821568000000), (9402229594024060151827/1554005006602186752000000), (157764412357882193959/3108010013204373504000000)],
    ![(399922247/7680000000), (144816660386615911/6218409553920000000), (86832108625789602808663/11655037549516400640000000), (181971826790861245727/2590008344336977920000000)],
    ![(125142191/1920000000), (94993949368194617/3109204776960000000), (65603994139548183074101/5827518774758200320000000), (7410995028414615862723/3885012516505466880000000)]]

theorem oldJunction_lower2 (i : Fin 3) (j : Fin 4) :
    (121453290708413616307/3885012516505466880000000) ≤ oldJunction_coeff2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunction_coeff2]

theorem oldJunction_identity2 (δ p : ℝ) :
    oldJunction δ p = tensor oldJunction_coeff2
      ((δ-(15/32))/((9/16)-(15/32))) ((p-0)/((1/2)-0)) := by
  norm_num [oldJunction, tensor, basis2, basis3, oldJunction_coeff2, Fin.sum_univ_succ]
  ring

theorem oldJunction_box2 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < oldJunction δ p := by
  rw [oldJunction_identity2]
  exact tensor_pos (by norm_num : (0:ℝ)<(121453290708413616307/3885012516505466880000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) oldJunction_lower2

def oldJunction_coeff3 : Fin 3 → Fin 4 → ℝ := ![
    ![(125142191/1920000000), (94993949368194617/3109204776960000000), (65603994139548183074101/5827518774758200320000000), (7410995028414615862723/3885012516505466880000000)],
    ![(350930899/3840000000), (7008259385898397/155460238848000000), (2749496844821373660341/145687969368955008000000), (1807255800405938654249/323751043042122240000000)],
    ![(64884677/480000000), (14083805585613797/194325298560000000), (487214674563789196973/13489626793421760000000), (4013267777205340706951/242813282281591680000000)]]

theorem oldJunction_lower3 (i : Fin 3) (j : Fin 4) :
    (121453290708413616307/3885012516505466880000000) ≤ oldJunction_coeff3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunction_coeff3]

theorem oldJunction_identity3 (δ p : ℝ) :
    oldJunction δ p = tensor oldJunction_coeff3
      ((δ-(9/16))/((3/4)-(9/16))) ((p-0)/((1/2)-0)) := by
  norm_num [oldJunction, tensor, basis2, basis3, oldJunction_coeff3, Fin.sum_univ_succ]
  ring

theorem oldJunction_box3 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < oldJunction δ p := by
  rw [oldJunction_identity3]
  exact tensor_pos (by norm_num : (0:ℝ)<(121453290708413616307/3885012516505466880000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) oldJunction_lower3

theorem oldJunction_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldJunction δ p := by
  rcases hδ with ⟨hd0,hd1⟩
  rcases hp with ⟨hp0,hp1⟩
  rcases le_total δ (3/8) with h8 | h8
  · exact oldJunction_box0 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  · rcases le_total δ (9/16) with h9 | h9
    · rcases le_total δ (15/32) with h10 | h10
      · exact oldJunction_box1 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      · exact oldJunction_box2 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    · exact oldJunction_box3 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩

#print axioms oldJunction_pos

def oldHalf (δ p : ℝ) : ℝ :=
    (330057223/600000000) +
    (-7012289151374971/20242218600000000)*p^1 +
    (-1267557223/1500000000)*δ^1 +
    (2146771485289529/16868515500000000)*δ^1*p^1 +
    (280259955725432281267/1138187260694961000000)*δ^1*p^2 +
    (1/2)*δ^2 +
    (-24995524938329/84342577500000)*δ^2*p^1 +
    (14840119436671/84342577500000)*δ^2*p^2 +
    (-40610477746684/379395753564987)*δ^2*p^3

def oldHalf_coeff0 : Fin 3 → Fin 4 → ℝ := ![
    ![(330057223/600000000), (59798615433374507/121453311600000000), (3299145392624971/7590831975000000), (3051602475374971/8096887440000000)],
    ![(2798472791/12000000000), (445548140155847467/2429066232000000000), (643467291807585090439711/4552749042779844000000000), (108196740605248334113949/1011722009506632000000000)],
    ![(1185400561/6000000000), (155405466030358247/1214533116000000000), (124411948360979718539519/1517583014259948000000000), (39545774645346413553811/758791507129974000000000)]]

theorem oldHalf_lower0 (i : Fin 3) (j : Fin 4) :
    (39545774645346413553811/758791507129974000000000) ≤ oldHalf_coeff0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldHalf_coeff0]

theorem oldHalf_identity0 (δ p : ℝ) :
    oldHalf δ p = tensor oldHalf_coeff0
      ((δ-0)/((3/4)-0)) ((p-0)/((1/2)-0)) := by
  norm_num [oldHalf, tensor, basis2, basis3, oldHalf_coeff0, Fin.sum_univ_succ]
  ring

theorem oldHalf_box0 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < oldHalf δ p := by
  rw [oldHalf_identity0]
  exact tensor_pos (by norm_num : (0:ℝ)<(39545774645346413553811/758791507129974000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) oldHalf_lower0

theorem oldHalf_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldHalf δ p := by
  rcases hδ with ⟨hd0,hd1⟩
  rcases hp with ⟨hp0,hp1⟩
  exact oldHalf_box0 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩

#print axioms oldHalf_pos

end
end Cycle63.Arithmetic.Bernstein
