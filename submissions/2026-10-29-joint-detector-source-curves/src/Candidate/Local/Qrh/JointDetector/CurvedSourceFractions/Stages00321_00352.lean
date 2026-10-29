/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00321_00352
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99957574984362,99957437989013,99957300966465,99957163916722,99957026839786,99956889735660,99956752604348,99956615445852,99956478260176,99956341047322,99956203807293,99956066540092,99955929245722,99955791924187,99955654575488,99955517199629,99955379796613,99955242366443,99955104909122,99954967424652,99954829913037,99954692374280,99954554808383,99954417215349,99954279595182,99954141947884,99954004273458,99953866571907,99953728843235,99953591087443,99953453304535,99953315494514,99953177657383]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (320+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(4758598849793855135716/5952008028722325298659:Fraction),(14274560553108841821613/17855674086167325895977:Fraction),(226560706601883791615/283417842637582157079:Fraction),(4757362812604690571180/5951658028722675298659:Fraction),(71354264006820308304772/89273120430841879479885:Fraction),(4756538960910117424172/5951424695389575298659:Fraction),(7926878558763624783982/9918846714538375497765:Fraction),(71335728233202437870266/89267870430847129479885:Fraction),(71329550439561987700156/89266120430848879479885:Fraction),(1584963858844613503720/1983652676241125099553:Fraction),(2641377653781214631846/3306022978920458499255:Fraction),(23770340219449985665726/29753623476951376493295:Fraction),(7922760495589260942592/9917680047872875497765:Fraction),(14259733852903169201294/17851474086171525895977:Fraction),(71292493864479982537048/89255620430859379479885:Fraction),(7920702162976428979793/9917096714540125497765:Fraction),(4752009657660350542402/5950141362057525298659:Fraction),(23757990421817420002678/29750123476954876493295:Fraction),(7918644162429489809528/9916513381207375497765:Fraction),(14252324932158553967666/17849374086173625895977:Fraction),(71255451655642893830068/89245120430869879479885:Fraction),(16435819989179770852/20586705981746627331:Fraction),(23747702482174615417744/29747206810291126493295:Fraction),(128354840076827489051/160792559334910143207:Fraction),(879392158454205263792/1101705190504652833085:Fraction),(5478814956131821133164/6864336186990663806145:Fraction),(7913158336385101039172/9914957825653375497765:Fraction),(23737418071533282521417/29744290143627376493295:Fraction),(14241217122277576376549/17846224086176775895977:Fraction),(128288136211862574818/160773640416010143207:Fraction),(678035693271880204385/849786861246546471237:Fraction),(14237515957151685065584/17845174086177825895977:Fraction)]
abbrev p321 := params 0
abbrev ray321 := rays 0
def bank321 : Fin 1 → Cell := oneBank p321 ray321
theorem signs321 : ∀ j, Signs p321 (bank321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p322 := params 1
abbrev ray322 := rays 1
def bank322 : Fin 1 → Cell := oneBank p322 ray322
theorem signs322 : ∀ j, Signs p322 (bank322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p323 := params 2
abbrev ray323 := rays 2
def bank323 : Fin 1 → Cell := oneBank p323 ray323
theorem signs323 : ∀ j, Signs p323 (bank323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p324 := params 3
abbrev ray324 := rays 3
def bank324 : Fin 1 → Cell := oneBank p324 ray324
theorem signs324 : ∀ j, Signs p324 (bank324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p325 := params 4
abbrev ray325 := rays 4
def bank325 : Fin 1 → Cell := oneBank p325 ray325
theorem signs325 : ∀ j, Signs p325 (bank325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p326 := params 5
abbrev ray326 := rays 5
def bank326 : Fin 1 → Cell := oneBank p326 ray326
theorem signs326 : ∀ j, Signs p326 (bank326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p327 := params 6
abbrev ray327 := rays 6
def bank327 : Fin 1 → Cell := oneBank p327 ray327
theorem signs327 : ∀ j, Signs p327 (bank327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p328 := params 7
abbrev ray328 := rays 7
def bank328 : Fin 1 → Cell := oneBank p328 ray328
theorem signs328 : ∀ j, Signs p328 (bank328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p329 := params 8
abbrev ray329 := rays 8
def bank329 : Fin 1 → Cell := oneBank p329 ray329
theorem signs329 : ∀ j, Signs p329 (bank329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p330 := params 9
abbrev ray330 := rays 9
def bank330 : Fin 1 → Cell := oneBank p330 ray330
theorem signs330 : ∀ j, Signs p330 (bank330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p331 := params 10
abbrev ray331 := rays 10
def bank331 : Fin 1 → Cell := oneBank p331 ray331
theorem signs331 : ∀ j, Signs p331 (bank331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p332 := params 11
abbrev ray332 := rays 11
def bank332 : Fin 1 → Cell := oneBank p332 ray332
theorem signs332 : ∀ j, Signs p332 (bank332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p333 := params 12
abbrev ray333 := rays 12
def bank333 : Fin 1 → Cell := oneBank p333 ray333
theorem signs333 : ∀ j, Signs p333 (bank333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p334 := params 13
abbrev ray334 := rays 13
def bank334 : Fin 1 → Cell := oneBank p334 ray334
theorem signs334 : ∀ j, Signs p334 (bank334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p335 := params 14
abbrev ray335 := rays 14
def bank335 : Fin 1 → Cell := oneBank p335 ray335
theorem signs335 : ∀ j, Signs p335 (bank335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p336 := params 15
abbrev ray336 := rays 15
def bank336 : Fin 1 → Cell := oneBank p336 ray336
theorem signs336 : ∀ j, Signs p336 (bank336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p337 := params 16
abbrev ray337 := rays 16
def bank337 : Fin 1 → Cell := oneBank p337 ray337
theorem signs337 : ∀ j, Signs p337 (bank337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p338 := params 17
abbrev ray338 := rays 17
def bank338 : Fin 1 → Cell := oneBank p338 ray338
theorem signs338 : ∀ j, Signs p338 (bank338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p339 := params 18
abbrev ray339 := rays 18
def bank339 : Fin 1 → Cell := oneBank p339 ray339
theorem signs339 : ∀ j, Signs p339 (bank339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p340 := params 19
abbrev ray340 := rays 19
def bank340 : Fin 1 → Cell := oneBank p340 ray340
theorem signs340 : ∀ j, Signs p340 (bank340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p341 := params 20
abbrev ray341 := rays 20
def bank341 : Fin 1 → Cell := oneBank p341 ray341
theorem signs341 : ∀ j, Signs p341 (bank341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p342 := params 21
abbrev ray342 := rays 21
def bank342 : Fin 1 → Cell := oneBank p342 ray342
theorem signs342 : ∀ j, Signs p342 (bank342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p343 := params 22
abbrev ray343 := rays 22
def bank343 : Fin 1 → Cell := oneBank p343 ray343
theorem signs343 : ∀ j, Signs p343 (bank343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p344 := params 23
abbrev ray344 := rays 23
def bank344 : Fin 1 → Cell := oneBank p344 ray344
theorem signs344 : ∀ j, Signs p344 (bank344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p345 := params 24
abbrev ray345 := rays 24
def bank345 : Fin 1 → Cell := oneBank p345 ray345
theorem signs345 : ∀ j, Signs p345 (bank345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p346 := params 25
abbrev ray346 := rays 25
def bank346 : Fin 1 → Cell := oneBank p346 ray346
theorem signs346 : ∀ j, Signs p346 (bank346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p347 := params 26
abbrev ray347 := rays 26
def bank347 : Fin 1 → Cell := oneBank p347 ray347
theorem signs347 : ∀ j, Signs p347 (bank347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p348 := params 27
abbrev ray348 := rays 27
def bank348 : Fin 1 → Cell := oneBank p348 ray348
theorem signs348 : ∀ j, Signs p348 (bank348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p349 := params 28
abbrev ray349 := rays 28
def bank349 : Fin 1 → Cell := oneBank p349 ray349
theorem signs349 : ∀ j, Signs p349 (bank349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p350 := params 29
abbrev ray350 := rays 29
def bank350 : Fin 1 → Cell := oneBank p350 ray350
theorem signs350 : ∀ j, Signs p350 (bank350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p351 := params 30
abbrev ray351 := rays 30
def bank351 : Fin 1 → Cell := oneBank p351 ray351
theorem signs351 : ∀ j, Signs p351 (bank351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p352 := params 31
abbrev ray352 := rays 31
def bank352 : Fin 1 → Cell := oneBank p352 ray352
theorem signs352 : ∀ j, Signs p352 (bank352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00321_00352
