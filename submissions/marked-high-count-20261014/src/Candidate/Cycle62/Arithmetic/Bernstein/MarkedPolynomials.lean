import Candidate.Cycle62.Arithmetic.Bernstein.Basis

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Cycle62.Arithmetic.Bernstein
noncomputable section
open Cycle62.Arithmetic.Bernstein

def newRow (δ p : ℝ) : ℝ :=
    (783947/12000000) +
    (-832776706789/20242332000000)*p^1 +
    (-16918369/60000000)*δ^1 +
    (341216930502159827/2153828736000000000)*δ^1*p^1 +
    (33265427525860826533/781839831168000000000)*δ^1*p^2 +
    (1/2)*δ^2 +
    (-174948418222852864489/217177730880000000000)*δ^2*p^1 +
    (36461337149514591837/72392576960000000000)*δ^2*p^2 +
    (-176873735806859/1303066385280000)*δ^2*p^3

def newRow_coeff0 : Fin 3 → Fin 4 → ℝ := ![
    ![(783947/12000000), (7101681015413/121453992000000), (391806519289/7590874500000), (362408506789/8096932800000)],
    ![(11960653/960000000), (792074049166461946003/75056623792128000000000), (82225264400448454283/8830191034368000000000), (87420478257327068881/10007549838950400000000)],
    ![(14352773/480000000), (621035017931075469203/44150955171840000000000), (328005332869852474327/60045299033702400000000), (77557983716086618843/45488862904320000000000)]]

theorem newRow_lower0 (i : Fin 3) (j : Fin 4) :
    (5460160314393190067/51238655175426048000000000) ≤ newRow_coeff0 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(5460160314393190067/51238655175426048000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower0

def newRow_coeff1 : Fin 3 → Fin 4 → ℝ := ![
    ![(14352773/480000000), (621035017931075469203/44150955171840000000000), (328005332869852474327/60045299033702400000000), (77557983716086618843/45488862904320000000000)],
    ![(246389261/7680000000), (719815018609834110149/49624214077440000000000), (11964580989528113899093/2401811961348096000000000), (3307216475026221821407/4003019935580160000000000)],
    ![(135785827/3840000000), (756479143247417644731991/48036239226961920000000000), (98016628240258574145239/19214495690784768000000000), (12821998925388152996213/32024159484641280000000000)]]

theorem newRow_lower1 (i : Fin 3) (j : Fin 4) :
    (5460160314393190067/51238655175426048000000000) ≤ newRow_coeff1 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(5460160314393190067/51238655175426048000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower1

def newRow_coeff2 : Fin 3 → Fin 4 → ℝ := ![
    ![(135785827/3840000000), (756479143247417644731991/48036239226961920000000000), (98016628240258574145239/19214495690784768000000000), (12821998925388152996213/32024159484641280000000000)],
    ![(568325701/15360000000), (1572656491727933515571741/96072478453923840000000000), (198333236804550811242973/38428991381569536000000000), (12008264975954684417383/64048318969282560000000000)],
    ![(149431711/3840000000), (3303312760649852401335391/192144956907847680000000000), (412811473183330491935327/76857982763139072000000000), (11252420063359709203853/128096637938565120000000000)]]

theorem newRow_lower2 (i : Fin 3) (j : Fin 4) :
    (5460160314393190067/51238655175426048000000000) ≤ newRow_coeff2 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(5460160314393190067/51238655175426048000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower2

def newRow_coeff3 : Fin 3 → Fin 4 → ℝ := ![
    ![(149431711/3840000000), (3303312760649852401335391/192144956907847680000000000), (412811473183330491935327/76857982763139072000000000), (11252420063359709203853/128096637938565120000000000)],
    ![(1224854831/30720000000), (614965936226699106623881/34935446710517760000000000), (168353589188177970664007/30743193105255628800000000), (572984131657044633929/15070192698654720000000000)],
    ![(1256365349/30720000000), (13883853518103140004085591/768579827631390720000000000), (1727370929956398989083223/307431931052556288000000000), (8460596560333781810933/512386551754260480000000000)]]

theorem newRow_lower3 (i : Fin 3) (j : Fin 4) :
    (5460160314393190067/51238655175426048000000000) ≤ newRow_coeff3 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(5460160314393190067/51238655175426048000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower3

def newRow_coeff4 : Fin 3 → Fin 4 → ℝ := ![
    ![(1256365349/30720000000), (13883853518103140004085591/768579827631390720000000000), (1727370929956398989083223/307431931052556288000000000), (8460596560333781810933/512386551754260480000000000)],
    ![(39753769/960000000), (28122309957322039666531391/1537159655262781440000000000), (3498576897987417260609599/614863862105112576000000000), (5900329204661827879213/1024773103508520960000000000)],
    ![(5153612843/122880000000), (56992429123603387567759591/3074319310525562880000000000), (1419273782210046925929979/245945544842045030400000000), (4266286438405767792293/2049546207017041920000000000)]]

theorem newRow_lower4 (i : Fin 3) (j : Fin 4) :
    (5460160314393190067/51238655175426048000000000) ≤ newRow_coeff4 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(5460160314393190067/51238655175426048000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower4

def newRow_coeff5 : Fin 3 → Fin 4 → ℝ := ![
    ![(5153612843/122880000000), (56992429123603387567759591/3074319310525562880000000000), (1419273782210046925929979/245945544842045030400000000), (4266286438405767792293/2049546207017041920000000000)],
    ![(10372356097/245760000000), (114732667456166083370215991/6148638621051125760000000000), (14291952937175869367730487/2459455448420450304000000000), (998200905893647618453/4099092414034083840000000000)],
    ![(20877082391/491520000000), (230999556696978572127801991/12297277242102251520000000000), (28793881143428700495866759/4918910896840900608000000000), (130455793731372983983/745289529824378880000000000)]]

theorem newRow_lower5 (i : Fin 3) (j : Fin 4) :
    (5460160314393190067/51238655175426048000000000) ≤ newRow_coeff5 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(5460160314393190067/51238655175426048000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower5

def newRow_coeff6 : Fin 3 → Fin 4 → ℝ := ![
    ![(20877082391/491520000000), (230999556696978572127801991/12297277242102251520000000000), (28793881143428700495866759/4918910896840900608000000000), (130455793731372983983/745289529824378880000000000)],
    ![(5252363147/122880000000), (58133444620406244378793/3074319310525562880000000), (906370512890801945508517/153715965526278144000000000), (5460160314393190067/51238655175426048000000000)],
    ![(16518697/384000000), (9144789204414030149239/480362392269619200000000), (5708081390724372179731/960724784539238400000000), (578890368384933653/320241594846412800000000)]]

theorem newRow_lower6 (i : Fin 3) (j : Fin 4) :
    (5460160314393190067/51238655175426048000000000) ≤ newRow_coeff6 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(5460160314393190067/51238655175426048000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower6

def newRow_coeff7 : Fin 3 → Fin 4 → ℝ := ![
    ![(16518697/384000000), (9144789204414030149239/480362392269619200000000), (5708081390724372179731/960724784539238400000000), (578890368384933653/320241594846412800000000)],
    ![(198806863/3840000000), (5555410321815886515461/240181196134809600000000), (17731458289359732073549/2401811961348096000000000), (45028375234560431339/800603987116032000000000)],
    ![(62325439/960000000), (91381167199756703947879/3002264951685120000000000), (13482616282494652734983/1200905980674048000000000), (349851161513072018287/181955451617280000000000)]]

theorem newRow_lower7 (i : Fin 3) (j : Fin 4) :
    (5460160314393190067/51238655175426048000000000) ≤ newRow_coeff7 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(5460160314393190067/51238655175426048000000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) newRow_lower7

def newRow_coeff8 : Fin 3 → Fin 4 → ℝ := ![
    ![(62325439/960000000), (91381167199756703947879/3002264951685120000000000), (13482616282494652734983/1200905980674048000000000), (349851161513072018287/181955451617280000000000)],
    ![(175145771/1920000000), (16907280444234118619639/375283118960640000000000), (113581952790621130657/6004529903370240000000), (1414993306719821805847/250188745973760000000000)],
    ![(32423833/240000000), (13608667914736131996421/187641559480320000000000), (247131839544973540183/6823329435648000000000), (2081180374497933763223/125094372986880000000000)]]

theorem newRow_lower8 (i : Fin 3) (j : Fin 4) :
    (5460160314393190067/51238655175426048000000000) ≤ newRow_coeff8 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(5460160314393190067/51238655175426048000000000))
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
    (15871/240000) +
    (-16859556977/404846640000)*p^1 +
    (-679003/2400000)*δ^1 +
    (52977624499/337372200000)*δ^1*p^1 +
    (6222325604194847/142275001666050000)*δ^1*p^2 +
    (1/2)*δ^2 +
    (-542597446009/674744400000)*δ^2*p^1 +
    (9654325421/19168875000)*δ^2*p^2 +
    (-129155037274/948500011107)*δ^2*p^3

def oldJunction_coeff0 : Fin 3 → Fin 4 → ℝ := ![
    ![(15871/240000), (143773468609/2429079840000), (7932119477/151817490000), (7336956977/161938656000)],
    ![(502351/38400000), (429404322691/38865277440000), (117745867104560407/12140800142169600000), (21930026070392309/2428160028433920000)],
    ![(582671/19200000), (11172828310517/777305548800000), (2064763900447645277/364224004265088000000), (49623993969540061/26979555871488000000)]]

theorem oldJunction_lower0 (i : Fin 3) (j : Fin 4) :
    (8015424318014369/194252802274713600000) ≤ oldJunction_coeff0 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(8015424318014369/194252802274713600000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) oldJunction_lower0

def oldJunction_coeff1 : Fin 3 → Fin 4 → ℝ := ![
    ![(582671/19200000), (11172828310517/777305548800000), (2064763900447645277/364224004265088000000), (49623993969540061/26979555871488000000)],
    ![(5324359/153600000), (9455211019753/621844439040000), (271657739564056567/58275840682414080000), (8015424318014369/194252802274713600000)],
    ![(133247/3072000), (47889470635921/2487377756160000), (471002872192564163/77701120909885440000), (9465625867650749/155402241819770880000)]]

theorem oldJunction_lower1 (i : Fin 3) (j : Fin 4) :
    (8015424318014369/194252802274713600000) ≤ oldJunction_coeff1 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(8015424318014369/194252802274713600000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) oldJunction_lower1

def oldJunction_coeff2 : Fin 3 → Fin 4 → ℝ := ![
    ![(133247/3072000), (47889470635921/2487377756160000), (471002872192564163/77701120909885440000), (9465625867650749/155402241819770880000)],
    ![(8000341/153600000), (5795809719283/248737775616000), (15812602499083261/2119121479360512000), (10432426900741669/129501868183142400000)],
    ![(2503333/38400000), (95034446026613/3109222195200000), (16418497059827236633/1456896017060352000000), (1862795943234423541/971264011373568000000)]]

theorem oldJunction_lower2 (i : Fin 3) (j : Fin 4) :
    (8015424318014369/194252802274713600000) ≤ oldJunction_coeff2 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(8015424318014369/194252802274713600000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) oldJunction_lower2

def oldJunction_coeff3 : Fin 3 → Fin 4 → ℝ := ![
    ![(2503333/38400000), (95034446026613/3109222195200000), (16418497059827236633/1456896017060352000000), (1862795943234423541/971264011373568000000)],
    ![(7019657/76800000), (35052023774441/777305548800000), (3439145342905278253/182112002132544000000), (452658452182678799/80938667614464000000)],
    ![(1297831/9600000), (14086619345417/194326387200000), (121846570220950321/3372444483936000000), (91266396106445059/5518545519168000000)]]

theorem oldJunction_lower3 (i : Fin 3) (j : Fin 4) :
    (8015424318014369/194252802274713600000) ≤ oldJunction_coeff3 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(8015424318014369/194252802274713600000))
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
    (33007123/60000000) +
    (-35063037670301/101211660000000)*p^1 +
    (-126757123/150000000)*δ^1 +
    (975996347609/7667550000000)*δ^1*p^1 +
    (17515414856377861/71137500833025000)*δ^1*p^2 +
    (1/2)*δ^2 +
    (-7811488093/26357203125)*δ^2*p^1 +
    (18548750753/105428812500)*δ^2*p^2 +
    (-101515006024/948500011107)*δ^2*p^3

def oldHalf_coeff0 : Fin 3 → Fin 4 → ℝ := ![
    ![(33007123/60000000), (299007533395117/607269960000000), (16496530982801/37954372500000), (15258763870301/40484664000000)],
    ![(279871091/1200000000), (2227984655619377/12145399200000000), (5027778453882654203/35568750416512500000), (27053568992808154139/252933336295200000000)],
    ![(118549861/600000000), (70647994669037/552063600000000), (7777141751766894821/94850001110700000000), (1797937109625543697/34490909494800000000)]]

theorem oldHalf_lower0 (i : Fin 3) (j : Fin 4) :
    (1797937109625543697/34490909494800000000) ≤ oldHalf_coeff0 i j := by
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
  exact tensor_pos (by norm_num : (0:ℝ)<(1797937109625543697/34490909494800000000))
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp) oldHalf_lower0

theorem oldHalf_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldHalf δ p := by
  rcases hδ with ⟨hd0,hd1⟩
  rcases hp with ⟨hp0,hp1⟩
  exact oldHalf_box0 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩

#print axioms oldHalf_pos

end
end Cycle62.Arithmetic.Bernstein
