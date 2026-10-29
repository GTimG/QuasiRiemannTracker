/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00705_00736
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99902995617897,99902848387757,99902701131493,99902553849106,99902406540600,99902259205976,99902111845238,99901964458388,99901817045430,99901669606365,99901522141196,99901374649926,99901227132558,99901079589093,99900932019535,99900784423887,99900636802150,99900489154328,99900341480424,99900193780440,99900046054378,99899898302242,99899750524033,99899602719755,99899454889410,99899307033001,99899159150530,99899011242000,99898863307413,99898715346772,99898567360080,99898419347340,99898271308554]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (704+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(23011940216624788795882/29536040143835626493295:Fraction),(23009932509735019211939/29535456810502876493295:Fraction),(69023776638486762249698/88604620431510379479885:Fraction),(1533727874264258567456/1968952676255825099553:Fraction),(1533594095007967281560/1968913787366975099553:Fraction),(69005712802973146233926/88599370431515629479885:Fraction),(22999897853586924838208/29532540143839126493295:Fraction),(3285412995843898778672/4218850972929482356185:Fraction),(1971075842713375863136/2531260583757739413711:Fraction),(4598775644760829907159/5906158028768175298659:Fraction),(1094851064734153792276/1406200324309910785395:Fraction),(9852799725616381411328/12655552918789447068555:Fraction),(22987860436961579710016/29529040143842626493295:Fraction),(4597170875780125253419/5905691362101975298659:Fraction),(13790309438627407696552/17716724086306275895977:Fraction),(7660614561777104677301/9842430047948125497765:Fraction),(170221024013044574400/218716346744530566617:Fraction),(13786699882638996460904/17715674086307325895977:Fraction),(22975827969198270316036/29525540143846126493295:Fraction),(13784293884139910976770/17714974086308025895977:Fraction),(68915454740344296614864/88573120431541879479885:Fraction),(7656604564308581263616/9841263381282625497765:Fraction),(1093705194028626137116/1405866990976910785395:Fraction),(1968497553934283601323/2530510583758489413711:Fraction),(218702861454743339224/281162287084282157079:Fraction),(68885389347740700287692/88564370431550629479885:Fraction),(13775875671248878780724/17712524086310475895977:Fraction),(4591557730611345487150/5904058028770275298659:Fraction),(9838193684784470252317/12651302918793697068555:Fraction),(620372481392867317082/797814148032050716035:Fraction),(4590355658835596400878/5903708028770625298659:Fraction),(1059220389994757466268/1362367237408632761229:Fraction)]
abbrev p705 := params 0
abbrev ray705 := rays 0
def bank705 : Fin 1 → Cell := oneBank p705 ray705
theorem signs705 : ∀ j, Signs p705 (bank705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p706 := params 1
abbrev ray706 := rays 1
def bank706 : Fin 1 → Cell := oneBank p706 ray706
theorem signs706 : ∀ j, Signs p706 (bank706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p707 := params 2
abbrev ray707 := rays 2
def bank707 : Fin 1 → Cell := oneBank p707 ray707
theorem signs707 : ∀ j, Signs p707 (bank707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p708 := params 3
abbrev ray708 := rays 3
def bank708 : Fin 1 → Cell := oneBank p708 ray708
theorem signs708 : ∀ j, Signs p708 (bank708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p709 := params 4
abbrev ray709 := rays 4
def bank709 : Fin 1 → Cell := oneBank p709 ray709
theorem signs709 : ∀ j, Signs p709 (bank709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p710 := params 5
abbrev ray710 := rays 5
def bank710 : Fin 1 → Cell := oneBank p710 ray710
theorem signs710 : ∀ j, Signs p710 (bank710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p711 := params 6
abbrev ray711 := rays 6
def bank711 : Fin 1 → Cell := oneBank p711 ray711
theorem signs711 : ∀ j, Signs p711 (bank711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p712 := params 7
abbrev ray712 := rays 7
def bank712 : Fin 1 → Cell := oneBank p712 ray712
theorem signs712 : ∀ j, Signs p712 (bank712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p713 := params 8
abbrev ray713 := rays 8
def bank713 : Fin 1 → Cell := oneBank p713 ray713
theorem signs713 : ∀ j, Signs p713 (bank713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p714 := params 9
abbrev ray714 := rays 9
def bank714 : Fin 1 → Cell := oneBank p714 ray714
theorem signs714 : ∀ j, Signs p714 (bank714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p715 := params 10
abbrev ray715 := rays 10
def bank715 : Fin 1 → Cell := oneBank p715 ray715
theorem signs715 : ∀ j, Signs p715 (bank715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p716 := params 11
abbrev ray716 := rays 11
def bank716 : Fin 1 → Cell := oneBank p716 ray716
theorem signs716 : ∀ j, Signs p716 (bank716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p717 := params 12
abbrev ray717 := rays 12
def bank717 : Fin 1 → Cell := oneBank p717 ray717
theorem signs717 : ∀ j, Signs p717 (bank717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p718 := params 13
abbrev ray718 := rays 13
def bank718 : Fin 1 → Cell := oneBank p718 ray718
theorem signs718 : ∀ j, Signs p718 (bank718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p719 := params 14
abbrev ray719 := rays 14
def bank719 : Fin 1 → Cell := oneBank p719 ray719
theorem signs719 : ∀ j, Signs p719 (bank719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p720 := params 15
abbrev ray720 := rays 15
def bank720 : Fin 1 → Cell := oneBank p720 ray720
theorem signs720 : ∀ j, Signs p720 (bank720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p721 := params 16
abbrev ray721 := rays 16
def bank721 : Fin 1 → Cell := oneBank p721 ray721
theorem signs721 : ∀ j, Signs p721 (bank721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p722 := params 17
abbrev ray722 := rays 17
def bank722 : Fin 1 → Cell := oneBank p722 ray722
theorem signs722 : ∀ j, Signs p722 (bank722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p723 := params 18
abbrev ray723 := rays 18
def bank723 : Fin 1 → Cell := oneBank p723 ray723
theorem signs723 : ∀ j, Signs p723 (bank723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p724 := params 19
abbrev ray724 := rays 19
def bank724 : Fin 1 → Cell := oneBank p724 ray724
theorem signs724 : ∀ j, Signs p724 (bank724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p725 := params 20
abbrev ray725 := rays 20
def bank725 : Fin 1 → Cell := oneBank p725 ray725
theorem signs725 : ∀ j, Signs p725 (bank725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p726 := params 21
abbrev ray726 := rays 21
def bank726 : Fin 1 → Cell := oneBank p726 ray726
theorem signs726 : ∀ j, Signs p726 (bank726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p727 := params 22
abbrev ray727 := rays 22
def bank727 : Fin 1 → Cell := oneBank p727 ray727
theorem signs727 : ∀ j, Signs p727 (bank727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p728 := params 23
abbrev ray728 := rays 23
def bank728 : Fin 1 → Cell := oneBank p728 ray728
theorem signs728 : ∀ j, Signs p728 (bank728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p729 := params 24
abbrev ray729 := rays 24
def bank729 : Fin 1 → Cell := oneBank p729 ray729
theorem signs729 : ∀ j, Signs p729 (bank729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p730 := params 25
abbrev ray730 := rays 25
def bank730 : Fin 1 → Cell := oneBank p730 ray730
theorem signs730 : ∀ j, Signs p730 (bank730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p731 := params 26
abbrev ray731 := rays 26
def bank731 : Fin 1 → Cell := oneBank p731 ray731
theorem signs731 : ∀ j, Signs p731 (bank731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p732 := params 27
abbrev ray732 := rays 27
def bank732 : Fin 1 → Cell := oneBank p732 ray732
theorem signs732 : ∀ j, Signs p732 (bank732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p733 := params 28
abbrev ray733 := rays 28
def bank733 : Fin 1 → Cell := oneBank p733 ray733
theorem signs733 : ∀ j, Signs p733 (bank733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p734 := params 29
abbrev ray734 := rays 29
def bank734 : Fin 1 → Cell := oneBank p734 ray734
theorem signs734 : ∀ j, Signs p734 (bank734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p735 := params 30
abbrev ray735 := rays 30
def bank735 : Fin 1 → Cell := oneBank p735 ray735
theorem signs735 : ∀ j, Signs p735 (bank735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p736 := params 31
abbrev ray736 := rays 31
def bank736 : Fin 1 → Cell := oneBank p736 ray736
theorem signs736 : ∀ j, Signs p736 (bank736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00705_00736
