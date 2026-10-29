/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00513_00544
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99930776550915,99930634386650,99930492195739,99930349978183,99930207733987,99930065463152,99929923165682,99929780841579,99929638490846,99929496113486,99929353709501,99929211278895,99929068821670,99928926337829,99928783827374,99928641290309,99928498726636,99928356136358,99928213519478,99928070875999,99927928205923,99927785509253,99927642785992,99927500036143,99927357259709,99927214456692,99927071627095,99926928770921,99926785888173,99926642978853,99926500042964,99926357080510,99926214091492]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (512+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(1559995781408414198827/1976536009581575099553:Fraction),(4679580490870791259300/5929491362078175298659:Fraction),(4679173785459330672455/5929374695411625298659:Fraction),(23393834930788307126542/29646290143725376493295:Fraction),(379326507096677085748/480741191519880429621:Fraction),(23389767947835124219786/29645123477059876493295:Fraction),(23387734558347040395592/29644540143727126493295:Fraction),(7795233835195696560718/9881318936798125497765:Fraction),(1895973112417606281904/2403516768410402148105:Fraction),(23381635604136869597128/29642790143728876493295:Fraction),(14027761653278833762900/17785324086237675895977:Fraction),(4675514048715422805766/5928324695412675298659:Fraction),(4675107533076564950272/5928208028746125298659:Fraction),(23373505424000862901111/29640456810397876493295:Fraction),(14022883869798201728240/17783924086239075895977:Fraction),(23369441145500328211982/29639290143732376493295:Fraction),(70102227325200819330068/88916120431198879479885:Fraction),(188938358531277033536/239661375825338623935:Fraction),(23363345641685229219968/29637540143734126493295:Fraction),(70083941426864485148717/88910870431204129479885:Fraction),(14015569629766912747724/17781824086241175895977:Fraction),(7785750384742981310242/9878596714578625497765:Fraction),(70065660996813915615668/88905620431209379479885:Fraction),(23353189444112830889842/29634623477070376493295:Fraction),(4670231697951587547746/5926808028747525298659:Fraction),(7783042624127745364442/9877818936801625497765:Fraction),(14008258313298125672612/17779724086243275895977:Fraction),(23345066842285539023146/29632290143739376493295:Fraction),(70029109288743117507104/88895120431219879479885:Fraction),(23341006353912650460839/29631123477073876493295:Fraction),(172881305274833474084/219485482546230566617:Fraction),(4667389281471411945008/5925991362081675298659:Fraction)]
abbrev p513 := params 0
abbrev ray513 := rays 0
def bank513 : Fin 1 → Cell := oneBank p513 ray513
theorem signs513 : ∀ j, Signs p513 (bank513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p514 := params 1
abbrev ray514 := rays 1
def bank514 : Fin 1 → Cell := oneBank p514 ray514
theorem signs514 : ∀ j, Signs p514 (bank514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p515 := params 2
abbrev ray515 := rays 2
def bank515 : Fin 1 → Cell := oneBank p515 ray515
theorem signs515 : ∀ j, Signs p515 (bank515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p516 := params 3
abbrev ray516 := rays 3
def bank516 : Fin 1 → Cell := oneBank p516 ray516
theorem signs516 : ∀ j, Signs p516 (bank516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p517 := params 4
abbrev ray517 := rays 4
def bank517 : Fin 1 → Cell := oneBank p517 ray517
theorem signs517 : ∀ j, Signs p517 (bank517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p518 := params 5
abbrev ray518 := rays 5
def bank518 : Fin 1 → Cell := oneBank p518 ray518
theorem signs518 : ∀ j, Signs p518 (bank518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p519 := params 6
abbrev ray519 := rays 6
def bank519 : Fin 1 → Cell := oneBank p519 ray519
theorem signs519 : ∀ j, Signs p519 (bank519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p520 := params 7
abbrev ray520 := rays 7
def bank520 : Fin 1 → Cell := oneBank p520 ray520
theorem signs520 : ∀ j, Signs p520 (bank520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p521 := params 8
abbrev ray521 := rays 8
def bank521 : Fin 1 → Cell := oneBank p521 ray521
theorem signs521 : ∀ j, Signs p521 (bank521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p522 := params 9
abbrev ray522 := rays 9
def bank522 : Fin 1 → Cell := oneBank p522 ray522
theorem signs522 : ∀ j, Signs p522 (bank522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p523 := params 10
abbrev ray523 := rays 10
def bank523 : Fin 1 → Cell := oneBank p523 ray523
theorem signs523 : ∀ j, Signs p523 (bank523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p524 := params 11
abbrev ray524 := rays 11
def bank524 : Fin 1 → Cell := oneBank p524 ray524
theorem signs524 : ∀ j, Signs p524 (bank524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p525 := params 12
abbrev ray525 := rays 12
def bank525 : Fin 1 → Cell := oneBank p525 ray525
theorem signs525 : ∀ j, Signs p525 (bank525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p526 := params 13
abbrev ray526 := rays 13
def bank526 : Fin 1 → Cell := oneBank p526 ray526
theorem signs526 : ∀ j, Signs p526 (bank526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p527 := params 14
abbrev ray527 := rays 14
def bank527 : Fin 1 → Cell := oneBank p527 ray527
theorem signs527 : ∀ j, Signs p527 (bank527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p528 := params 15
abbrev ray528 := rays 15
def bank528 : Fin 1 → Cell := oneBank p528 ray528
theorem signs528 : ∀ j, Signs p528 (bank528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p529 := params 16
abbrev ray529 := rays 16
def bank529 : Fin 1 → Cell := oneBank p529 ray529
theorem signs529 : ∀ j, Signs p529 (bank529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p530 := params 17
abbrev ray530 := rays 17
def bank530 : Fin 1 → Cell := oneBank p530 ray530
theorem signs530 : ∀ j, Signs p530 (bank530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p531 := params 18
abbrev ray531 := rays 18
def bank531 : Fin 1 → Cell := oneBank p531 ray531
theorem signs531 : ∀ j, Signs p531 (bank531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p532 := params 19
abbrev ray532 := rays 19
def bank532 : Fin 1 → Cell := oneBank p532 ray532
theorem signs532 : ∀ j, Signs p532 (bank532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p533 := params 20
abbrev ray533 := rays 20
def bank533 : Fin 1 → Cell := oneBank p533 ray533
theorem signs533 : ∀ j, Signs p533 (bank533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p534 := params 21
abbrev ray534 := rays 21
def bank534 : Fin 1 → Cell := oneBank p534 ray534
theorem signs534 : ∀ j, Signs p534 (bank534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p535 := params 22
abbrev ray535 := rays 22
def bank535 : Fin 1 → Cell := oneBank p535 ray535
theorem signs535 : ∀ j, Signs p535 (bank535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p536 := params 23
abbrev ray536 := rays 23
def bank536 : Fin 1 → Cell := oneBank p536 ray536
theorem signs536 : ∀ j, Signs p536 (bank536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p537 := params 24
abbrev ray537 := rays 24
def bank537 : Fin 1 → Cell := oneBank p537 ray537
theorem signs537 : ∀ j, Signs p537 (bank537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p538 := params 25
abbrev ray538 := rays 25
def bank538 : Fin 1 → Cell := oneBank p538 ray538
theorem signs538 : ∀ j, Signs p538 (bank538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p539 := params 26
abbrev ray539 := rays 26
def bank539 : Fin 1 → Cell := oneBank p539 ray539
theorem signs539 : ∀ j, Signs p539 (bank539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p540 := params 27
abbrev ray540 := rays 27
def bank540 : Fin 1 → Cell := oneBank p540 ray540
theorem signs540 : ∀ j, Signs p540 (bank540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p541 := params 28
abbrev ray541 := rays 28
def bank541 : Fin 1 → Cell := oneBank p541 ray541
theorem signs541 : ∀ j, Signs p541 (bank541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p542 := params 29
abbrev ray542 := rays 29
def bank542 : Fin 1 → Cell := oneBank p542 ray542
theorem signs542 : ∀ j, Signs p542 (bank542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p543 := params 30
abbrev ray543 := rays 30
def bank543 : Fin 1 → Cell := oneBank p543 ray543
theorem signs543 : ∀ j, Signs p543 (bank543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p544 := params 31
abbrev ray544 := rays 31
def bank544 : Fin 1 → Cell := oneBank p544 ray544
theorem signs544 : ∀ j, Signs p544 (bank544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00513_00544
