/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource07
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource08 : Source := ⟨(497604200071/500000000000),(1052952527533/250000000000),(35550781757/1000000000000),(14111013051/20000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource08_valid : SeedSourceValid seedSource08 seedSource07 := by decide +kernel
#print axioms seedSource08_valid
end Record1252270103Finite
