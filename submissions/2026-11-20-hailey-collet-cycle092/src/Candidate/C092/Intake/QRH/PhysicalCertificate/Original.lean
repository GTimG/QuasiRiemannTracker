/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.PhysicalCertificate.Basic

/-! Exact original 57-cell cover, checked independently of price assumptions. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QRH.PhysicalCertificate

open QRH.Coverage

/-- Actual 57 rectangles in the pinned original return certificate. -/
def originalCells : List OriginalCell := [
  ⟨0, ⟨0, (3 / 4), 0, (1 / 2)⟩⟩,
  ⟨1, ⟨0, (3 / 8), 0, (1 / 2)⟩⟩,
  ⟨1, ⟨(3 / 8), (3 / 4), 0, (1 / 2)⟩⟩,
  ⟨2, ⟨0, (3 / 8), 0, (1 / 2)⟩⟩,
  ⟨2, ⟨(3 / 8), (3 / 4), 0, (1 / 2)⟩⟩,
  ⟨3, ⟨0, (3 / 16), 0, (1 / 4)⟩⟩,
  ⟨3, ⟨(3 / 16), (3 / 8), 0, (1 / 8)⟩⟩,
  ⟨3, ⟨(3 / 16), (9 / 32), (1 / 8), (1 / 4)⟩⟩,
  ⟨3, ⟨(9 / 32), (3 / 8), (1 / 8), (3 / 16)⟩⟩,
  ⟨3, ⟨(9 / 32), (3 / 8), (3 / 16), (1 / 4)⟩⟩,
  ⟨3, ⟨0, (3 / 16), (1 / 4), (1 / 2)⟩⟩,
  ⟨3, ⟨(3 / 16), (15 / 64), (1 / 4), (5 / 16)⟩⟩,
  ⟨3, ⟨(15 / 64), (9 / 32), (1 / 4), (5 / 16)⟩⟩,
  ⟨3, ⟨(3 / 16), (15 / 64), (5 / 16), (3 / 8)⟩⟩,
  ⟨3, ⟨(15 / 64), (9 / 32), (5 / 16), (3 / 8)⟩⟩,
  ⟨3, ⟨(9 / 32), (3 / 8), (1 / 4), (3 / 8)⟩⟩,
  ⟨3, ⟨(3 / 16), (15 / 64), (3 / 8), (7 / 16)⟩⟩,
  ⟨3, ⟨(15 / 64), (9 / 32), (3 / 8), (7 / 16)⟩⟩,
  ⟨3, ⟨(3 / 16), (15 / 64), (7 / 16), (1 / 2)⟩⟩,
  ⟨3, ⟨(15 / 64), (9 / 32), (7 / 16), (1 / 2)⟩⟩,
  ⟨3, ⟨(9 / 32), (3 / 8), (3 / 8), (7 / 16)⟩⟩,
  ⟨3, ⟨(9 / 32), (21 / 64), (7 / 16), (1 / 2)⟩⟩,
  ⟨3, ⟨(21 / 64), (3 / 8), (7 / 16), (15 / 32)⟩⟩,
  ⟨3, ⟨(21 / 64), (45 / 128), (15 / 32), (1 / 2)⟩⟩,
  ⟨3, ⟨(45 / 128), (3 / 8), (15 / 32), (31 / 64)⟩⟩,
  ⟨3, ⟨(45 / 128), (93 / 256), (31 / 64), (1 / 2)⟩⟩,
  ⟨3, ⟨(93 / 256), (189 / 512), (31 / 64), (63 / 128)⟩⟩,
  ⟨3, ⟨(189 / 512), (3 / 8), (31 / 64), (63 / 128)⟩⟩,
  ⟨3, ⟨(93 / 256), (189 / 512), (63 / 128), (1 / 2)⟩⟩,
  ⟨3, ⟨(189 / 512), (3 / 8), (63 / 128), (1 / 2)⟩⟩,
  ⟨3, ⟨(3 / 8), (3 / 4), 0, (1 / 4)⟩⟩,
  ⟨3, ⟨(3 / 8), (15 / 32), (1 / 4), (3 / 8)⟩⟩,
  ⟨3, ⟨(15 / 32), (9 / 16), (1 / 4), (3 / 8)⟩⟩,
  ⟨3, ⟨(3 / 8), (15 / 32), (3 / 8), (7 / 16)⟩⟩,
  ⟨3, ⟨(3 / 8), (27 / 64), (7 / 16), (15 / 32)⟩⟩,
  ⟨3, ⟨(3 / 8), (27 / 64), (15 / 32), (1 / 2)⟩⟩,
  ⟨3, ⟨(27 / 64), (15 / 32), (7 / 16), (15 / 32)⟩⟩,
  ⟨3, ⟨(27 / 64), (57 / 128), (15 / 32), (31 / 64)⟩⟩,
  ⟨3, ⟨(27 / 64), (111 / 256), (31 / 64), (63 / 128)⟩⟩,
  ⟨3, ⟨(27 / 64), (219 / 512), (63 / 128), (127 / 256)⟩⟩,
  ⟨3, ⟨(27 / 64), (435 / 1024), (127 / 256), (1 / 2)⟩⟩,
  ⟨3, ⟨(435 / 1024), (219 / 512), (127 / 256), (255 / 512)⟩⟩,
  ⟨3, ⟨(435 / 1024), (873 / 2048), (255 / 512), (511 / 1024)⟩⟩,
  ⟨3, ⟨(435 / 1024), (1743 / 4096), (511 / 1024), (1 / 2)⟩⟩,
  ⟨3, ⟨(1743 / 4096), (873 / 2048), (511 / 1024), (1023 / 2048)⟩⟩,
  ⟨3, ⟨(1743 / 4096), (3489 / 8192), (1023 / 2048), (2047 / 4096)⟩⟩,
  ⟨3, ⟨(1743 / 4096), (6975 / 16384), (2047 / 4096), (1 / 2)⟩⟩,
  ⟨3, ⟨(6975 / 16384), (3489 / 8192), (2047 / 4096), (4095 / 8192)⟩⟩,
  ⟨3, ⟨(6975 / 16384), (13953 / 32768), (4095 / 8192), (1 / 2)⟩⟩,
  ⟨3, ⟨(13953 / 32768), (3489 / 8192), (4095 / 8192), (1 / 2)⟩⟩,
  ⟨3, ⟨(3489 / 8192), (873 / 2048), (1023 / 2048), (1 / 2)⟩⟩,
  ⟨3, ⟨(873 / 2048), (219 / 512), (255 / 512), (1 / 2)⟩⟩,
  ⟨3, ⟨(219 / 512), (111 / 256), (63 / 128), (1 / 2)⟩⟩,
  ⟨3, ⟨(111 / 256), (57 / 128), (31 / 64), (1 / 2)⟩⟩,
  ⟨3, ⟨(57 / 128), (15 / 32), (15 / 32), (1 / 2)⟩⟩,
  ⟨3, ⟨(15 / 32), (9 / 16), (3 / 8), (1 / 2)⟩⟩,
  ⟨3, ⟨(9 / 16), (3 / 4), (1 / 4), (1 / 2)⟩⟩
]

/-- The full closed parameter rectangle, on each of the four physical edges. -/
def originalDomain : Box := ⟨0, 3 / 4, 0, 1 / 2⟩

/-- Exactly 57 cells are present in the imported original data. -/
theorem originalCells_length : originalCells.length = 57 := by decide

/-- Explicit closed partition certifying original physical edge 0. -/
def originalTree0 : CutTree := (.leaf 0)

/-- Kernel check of every actual rectangle used to cover physical edge 0. -/
theorem originalTree0_checked : originalTree0.check originalCells 0 originalDomain = true := by decide +kernel

/-- Explicit closed partition certifying original physical edge 1. -/
def originalTree1 : CutTree := (.uSplit (3 / 8) (.leaf 1) (.leaf 2))

/-- Kernel check of every actual rectangle used to cover physical edge 1. -/
theorem originalTree1_checked : originalTree1.check originalCells 1 originalDomain = true := by decide +kernel

/-- Explicit closed partition certifying original physical edge 2. -/
def originalTree2 : CutTree := (.uSplit (3 / 8) (.leaf 3) (.leaf 4))

/-- Kernel check of every actual rectangle used to cover physical edge 2. -/
theorem originalTree2_checked : originalTree2.check originalCells 2 originalDomain = true := by decide +kernel

/-- Explicit closed partition certifying original physical edge 3. -/
def originalTree3 : CutTree := (.uSplit (1743 / 4096) (.vSplit (15 / 32) (.uSplit (21 / 64) (.vSplit (5 / 16) (.uSplit (15 / 64) (.vSplit (1 / 4) (.uSplit (3 / 16) (.leaf 5) (.vSplit (1 / 8) (.leaf 6) (.leaf 7))) (.uSplit (3 / 16) (.leaf 10) (.leaf 11))) (.vSplit (3 / 16) (.uSplit (9 / 32) (.vSplit (1 / 8) (.leaf 6) (.leaf 7)) (.vSplit (1 / 8) (.leaf 6) (.leaf 8))) (.uSplit (9 / 32) (.vSplit (1 / 4) (.leaf 7) (.leaf 12)) (.vSplit (1 / 4) (.leaf 9) (.leaf 15))))) (.uSplit (15 / 64) (.vSplit (7 / 16) (.uSplit (3 / 16) (.leaf 10) (.vSplit (3 / 8) (.leaf 13) (.leaf 16))) (.uSplit (3 / 16) (.leaf 10) (.leaf 18))) (.vSplit (7 / 16) (.uSplit (9 / 32) (.vSplit (3 / 8) (.leaf 14) (.leaf 17)) (.vSplit (3 / 8) (.leaf 15) (.leaf 20))) (.uSplit (9 / 32) (.leaf 19) (.leaf 21))))) (.vSplit (1 / 4) (.vSplit (3 / 16) (.uSplit (3 / 8) (.vSplit (1 / 8) (.leaf 6) (.leaf 8)) (.leaf 30)) (.uSplit (3 / 8) (.leaf 9) (.leaf 30))) (.uSplit (27 / 64) (.vSplit (7 / 16) (.uSplit (3 / 8) (.vSplit (3 / 8) (.leaf 15) (.leaf 20)) (.vSplit (3 / 8) (.leaf 31) (.leaf 33))) (.uSplit (3 / 8) (.leaf 22) (.leaf 34))) (.vSplit (7 / 16) (.vSplit (3 / 8) (.leaf 31) (.leaf 33)) (.leaf 36))))) (.uSplit (93 / 256) (.uSplit (9 / 32) (.uSplit (15 / 64) (.uSplit (3 / 16) (.leaf 10) (.leaf 18)) (.leaf 19)) (.uSplit (45 / 128) (.uSplit (21 / 64) (.leaf 21) (.leaf 23)) (.vSplit (31 / 64) (.leaf 24) (.leaf 25)))) (.vSplit (127 / 256) (.uSplit (3 / 8) (.vSplit (63 / 128) (.uSplit (189 / 512) (.vSplit (31 / 64) (.leaf 24) (.leaf 26)) (.vSplit (31 / 64) (.leaf 24) (.leaf 27))) (.uSplit (189 / 512) (.leaf 28) (.leaf 29))) (.vSplit (63 / 128) (.uSplit (27 / 64) (.leaf 35) (.vSplit (31 / 64) (.leaf 37) (.leaf 38))) (.uSplit (27 / 64) (.leaf 35) (.leaf 39)))) (.uSplit (27 / 64) (.uSplit (3 / 8) (.uSplit (189 / 512) (.leaf 28) (.leaf 29)) (.leaf 35)) (.vSplit (511 / 1024) (.uSplit (435 / 1024) (.leaf 40) (.vSplit (255 / 512) (.leaf 41) (.leaf 42))) (.uSplit (435 / 1024) (.leaf 40) (.leaf 43))))))) (.vSplit (127 / 256) (.vSplit (15 / 32) (.vSplit (3 / 8) (.uSplit (9 / 16) (.uSplit (15 / 32) (.vSplit (1 / 4) (.leaf 30) (.leaf 31)) (.vSplit (1 / 4) (.leaf 30) (.leaf 32))) (.vSplit (1 / 4) (.leaf 30) (.leaf 56))) (.uSplit (9 / 16) (.uSplit (15 / 32) (.vSplit (7 / 16) (.leaf 33) (.leaf 36)) (.leaf 55)) (.leaf 56))) (.uSplit (57 / 128) (.uSplit (111 / 256) (.vSplit (63 / 128) (.vSplit (31 / 64) (.leaf 37) (.leaf 38)) (.uSplit (219 / 512) (.leaf 39) (.leaf 52))) (.vSplit (31 / 64) (.leaf 37) (.leaf 53))) (.uSplit (9 / 16) (.uSplit (15 / 32) (.leaf 54) (.leaf 55)) (.leaf 56)))) (.uSplit (219 / 512) (.vSplit (1023 / 2048) (.vSplit (511 / 1024) (.uSplit (873 / 2048) (.vSplit (255 / 512) (.leaf 41) (.leaf 42)) (.vSplit (255 / 512) (.leaf 41) (.leaf 51))) (.uSplit (873 / 2048) (.leaf 44) (.leaf 51))) (.uSplit (3489 / 8192) (.uSplit (13953 / 32768) (.vSplit (4095 / 8192) (.uSplit (6975 / 16384) (.vSplit (2047 / 4096) (.leaf 45) (.leaf 46)) (.vSplit (2047 / 4096) (.leaf 45) (.leaf 47))) (.uSplit (6975 / 16384) (.leaf 46) (.leaf 48))) (.vSplit (4095 / 8192) (.vSplit (2047 / 4096) (.leaf 45) (.leaf 47)) (.leaf 49))) (.uSplit (873 / 2048) (.leaf 50) (.leaf 51)))) (.uSplit (15 / 32) (.uSplit (57 / 128) (.uSplit (111 / 256) (.leaf 52) (.leaf 53)) (.leaf 54)) (.uSplit (9 / 16) (.leaf 55) (.leaf 56))))))

/-- Kernel check of every actual rectangle used to cover physical edge 3. -/
theorem originalTree3_checked : originalTree3.check originalCells 3 originalDomain = true := by decide +kernel

/-- Every real parameter point on every physical edge lies in an actual source cell. -/
theorem originalCells_cover (edge : Fin 4) {p : Point} (hp : originalDomain.Contains p) :
    ∃ cell ∈ originalCells, cell.edge = edge.val ∧ cell.box.Contains p := by
  fin_cases edge
  · exact originalTree0.sound originalCells 0 originalDomain originalTree0_checked hp
  · exact originalTree1.sound originalCells 1 originalDomain originalTree1_checked hp
  · exact originalTree2.sound originalCells 2 originalDomain originalTree2_checked hp
  · exact originalTree3.sound originalCells 3 originalDomain originalTree3_checked hp

end QRH.PhysicalCertificate
