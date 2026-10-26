/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource05
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource06 : Source := ⟨(498471183889/500000000000),(860670148917/200000000000),(33351088663/1000000000000),(719597099949/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource06_valid : SeedSourceValid seedSource06 seedSource05 := by decide +kernel
#print axioms seedSource06_valid
end Record1252270103Finite
