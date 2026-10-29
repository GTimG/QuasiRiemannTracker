/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00801_00832
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99888742770081,99888593043896,99888443291837,99888293513906,99888143710105,99887993880437,99887844024905,99887694143511,99887544236258,99887394303149,99887244344186,99887094359371,99886944348708,99886794312198,99886644249845,99886494161650,99886344047617,99886193907748,99886043742045,99885893550511,99885743333148,99885593089960,99885442820948,99885292526116,99885142205466,99884991859000,99884841486721,99884691088631,99884540664734,99884390215031,99884239739526,99884089238220,99883938711116]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (800+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(7606621946687549433241/9826680047963875497765:Fraction),(68453615321859129588586/88438370431676629479885:Fraction),(9778233449356067127964/12633802918811197068555:Fraction),(2534876028806928348076/3275365571543708499255:Fraction),(1955304926632120583263/2526660583762339413711:Fraction),(13685938379035100872969/17686274086336725895977:Fraction),(4561580825356807233980/5895308028779025298659:Fraction),(1954792362122734427447/2526510583762489413711:Fraction),(68411753990446185318868/88426120431688879479885:Fraction),(7600641679490855007167/9824930047965625497765:Fraction),(68399797262677639893584/88422620431692379479885:Fraction),(68393819218810273146611/88420870431694129479885:Fraction),(22795947399104688027574/29473040143898626493295:Fraction),(9768837854963339456128/12631052918813947068555:Fraction),(13675177758925074466124/17683124086339875895977:Fraction),(168814598551816573500/218305852917780566617:Fraction),(1953255344425150008043/2526060583762939413711:Fraction),(13671592301061425499550/17682074086340925895977:Fraction),(24110048316877785372/31184698564975795231:Fraction),(68346013474060116269288/88406870431708129479885:Fraction),(68340038565297598806922/88405120431709879479885:Fraction),(4555604392858200413248/5893558028780775298659:Fraction),(68328091815998397910472/88401620431713379479885:Fraction),(68322119975571874404028/88399870431715129479885:Fraction),(22772049314792462328544/29466040143905626493295:Fraction),(13662035144485277079820/17679274086343725895977:Fraction),(361397907531306700079/467696404400636928465:Fraction),(22766077711234598169452/29464290143907376493295:Fraction),(7588029196334980767712/9821235603524875497765:Fraction),(68286292209674857687588/88389370431725629479885:Fraction),(4552021511696034668032/5892508028781825298659:Fraction),(505735956773074744606/654710151346141699851:Fraction)]
abbrev p801 := params 0
abbrev ray801 := rays 0
def bank801 : Fin 1 → Cell := oneBank p801 ray801
theorem signs801 : ∀ j, Signs p801 (bank801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p802 := params 1
abbrev ray802 := rays 1
def bank802 : Fin 1 → Cell := oneBank p802 ray802
theorem signs802 : ∀ j, Signs p802 (bank802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p803 := params 2
abbrev ray803 := rays 2
def bank803 : Fin 1 → Cell := oneBank p803 ray803
theorem signs803 : ∀ j, Signs p803 (bank803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p804 := params 3
abbrev ray804 := rays 3
def bank804 : Fin 1 → Cell := oneBank p804 ray804
theorem signs804 : ∀ j, Signs p804 (bank804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p805 := params 4
abbrev ray805 := rays 4
def bank805 : Fin 1 → Cell := oneBank p805 ray805
theorem signs805 : ∀ j, Signs p805 (bank805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p806 := params 5
abbrev ray806 := rays 5
def bank806 : Fin 1 → Cell := oneBank p806 ray806
theorem signs806 : ∀ j, Signs p806 (bank806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p807 := params 6
abbrev ray807 := rays 6
def bank807 : Fin 1 → Cell := oneBank p807 ray807
theorem signs807 : ∀ j, Signs p807 (bank807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p808 := params 7
abbrev ray808 := rays 7
def bank808 : Fin 1 → Cell := oneBank p808 ray808
theorem signs808 : ∀ j, Signs p808 (bank808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p809 := params 8
abbrev ray809 := rays 8
def bank809 : Fin 1 → Cell := oneBank p809 ray809
theorem signs809 : ∀ j, Signs p809 (bank809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p810 := params 9
abbrev ray810 := rays 9
def bank810 : Fin 1 → Cell := oneBank p810 ray810
theorem signs810 : ∀ j, Signs p810 (bank810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p811 := params 10
abbrev ray811 := rays 10
def bank811 : Fin 1 → Cell := oneBank p811 ray811
theorem signs811 : ∀ j, Signs p811 (bank811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p812 := params 11
abbrev ray812 := rays 11
def bank812 : Fin 1 → Cell := oneBank p812 ray812
theorem signs812 : ∀ j, Signs p812 (bank812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p813 := params 12
abbrev ray813 := rays 12
def bank813 : Fin 1 → Cell := oneBank p813 ray813
theorem signs813 : ∀ j, Signs p813 (bank813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p814 := params 13
abbrev ray814 := rays 13
def bank814 : Fin 1 → Cell := oneBank p814 ray814
theorem signs814 : ∀ j, Signs p814 (bank814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p815 := params 14
abbrev ray815 := rays 14
def bank815 : Fin 1 → Cell := oneBank p815 ray815
theorem signs815 : ∀ j, Signs p815 (bank815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p816 := params 15
abbrev ray816 := rays 15
def bank816 : Fin 1 → Cell := oneBank p816 ray816
theorem signs816 : ∀ j, Signs p816 (bank816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p817 := params 16
abbrev ray817 := rays 16
def bank817 : Fin 1 → Cell := oneBank p817 ray817
theorem signs817 : ∀ j, Signs p817 (bank817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p818 := params 17
abbrev ray818 := rays 17
def bank818 : Fin 1 → Cell := oneBank p818 ray818
theorem signs818 : ∀ j, Signs p818 (bank818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p819 := params 18
abbrev ray819 := rays 18
def bank819 : Fin 1 → Cell := oneBank p819 ray819
theorem signs819 : ∀ j, Signs p819 (bank819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p820 := params 19
abbrev ray820 := rays 19
def bank820 : Fin 1 → Cell := oneBank p820 ray820
theorem signs820 : ∀ j, Signs p820 (bank820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p821 := params 20
abbrev ray821 := rays 20
def bank821 : Fin 1 → Cell := oneBank p821 ray821
theorem signs821 : ∀ j, Signs p821 (bank821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p822 := params 21
abbrev ray822 := rays 21
def bank822 : Fin 1 → Cell := oneBank p822 ray822
theorem signs822 : ∀ j, Signs p822 (bank822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p823 := params 22
abbrev ray823 := rays 22
def bank823 : Fin 1 → Cell := oneBank p823 ray823
theorem signs823 : ∀ j, Signs p823 (bank823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p824 := params 23
abbrev ray824 := rays 23
def bank824 : Fin 1 → Cell := oneBank p824 ray824
theorem signs824 : ∀ j, Signs p824 (bank824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p825 := params 24
abbrev ray825 := rays 24
def bank825 : Fin 1 → Cell := oneBank p825 ray825
theorem signs825 : ∀ j, Signs p825 (bank825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p826 := params 25
abbrev ray826 := rays 25
def bank826 : Fin 1 → Cell := oneBank p826 ray826
theorem signs826 : ∀ j, Signs p826 (bank826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p827 := params 26
abbrev ray827 := rays 26
def bank827 : Fin 1 → Cell := oneBank p827 ray827
theorem signs827 : ∀ j, Signs p827 (bank827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p828 := params 27
abbrev ray828 := rays 27
def bank828 : Fin 1 → Cell := oneBank p828 ray828
theorem signs828 : ∀ j, Signs p828 (bank828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p829 := params 28
abbrev ray829 := rays 28
def bank829 : Fin 1 → Cell := oneBank p829 ray829
theorem signs829 : ∀ j, Signs p829 (bank829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p830 := params 29
abbrev ray830 := rays 29
def bank830 : Fin 1 → Cell := oneBank p830 ray830
theorem signs830 : ∀ j, Signs p830 (bank830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p831 := params 30
abbrev ray831 := rays 30
def bank831 : Fin 1 → Cell := oneBank p831 ray831
theorem signs831 : ∀ j, Signs p831 (bank831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p832 := params 31
abbrev ray832 := rays 31
def bank832 : Fin 1 → Cell := oneBank p832 ray832
theorem signs832 : ∀ j, Signs p832 (bank832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00801_00832
