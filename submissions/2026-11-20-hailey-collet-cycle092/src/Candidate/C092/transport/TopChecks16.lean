/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.TopKernel
/-! Exact Q top-price row checks, split into bounded kernel reductions. -/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.Top
open QRH.Cycle092.TopData
namespace Batch16
def part00 : List Row := (group16.drop 0).take 25
theorem part00_checked : part00.all check = true := by decide +kernel
def part01 : List Row := (group16.drop 25).take 25
theorem part01_checked : part01.all check = true := by decide +kernel
def part02 : List Row := (group16.drop 50).take 25
theorem part02_checked : part02.all check = true := by decide +kernel
def part03 : List Row := (group16.drop 75).take 25
theorem part03_checked : part03.all check = true := by decide +kernel
def part04 : List Row := (group16.drop 100).take 25
theorem part04_checked : part04.all check = true := by decide +kernel
def part05 : List Row := (group16.drop 125).take 25
theorem part05_checked : part05.all check = true := by decide +kernel
def part06 : List Row := (group16.drop 150).take 25
theorem part06_checked : part06.all check = true := by decide +kernel
def part07 : List Row := (group16.drop 175).take 25
theorem part07_checked : part07.all check = true := by decide +kernel
def part08 : List Row := (group16.drop 200).take 25
theorem part08_checked : part08.all check = true := by decide +kernel
def part09 : List Row := (group16.drop 225).take 25
theorem part09_checked : part09.all check = true := by decide +kernel
def part10 : List Row := (group16.drop 250).take 25
theorem part10_checked : part10.all check = true := by decide +kernel
def part11 : List Row := (group16.drop 275).take 25
theorem part11_checked : part11.all check = true := by decide +kernel
def part12 : List Row := (group16.drop 300).take 3
theorem part12_checked : part12.all check = true := by decide +kernel
theorem assembled : group16 = part00 ++ part01 ++ part02 ++ part03 ++ part04 ++ part05 ++ part06 ++ part07 ++ part08 ++ part09 ++ part10 ++ part11 ++ part12 := by rfl
end Batch16
theorem group16_checked : group16.all check = true := by
  rw [Batch16.assembled]
  simp only [List.all_append, Batch16.part00_checked, Batch16.part01_checked, Batch16.part02_checked, Batch16.part03_checked, Batch16.part04_checked, Batch16.part05_checked, Batch16.part06_checked, Batch16.part07_checked, Batch16.part08_checked, Batch16.part09_checked, Batch16.part10_checked, Batch16.part11_checked, Batch16.part12_checked, Bool.and_true]
end QRH.Cycle092.Top
