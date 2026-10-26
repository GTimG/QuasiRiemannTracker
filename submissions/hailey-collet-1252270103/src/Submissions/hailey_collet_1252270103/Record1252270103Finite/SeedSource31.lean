/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource29
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource31 : Source := ⟨(123555901899/125000000000),(979378569533/250000000000),(5300816949/125000000000),(660667730523/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource31_valid : SeedSourceValid seedSource31 seedSource29 := by decide +kernel
#print axioms seedSource31_valid
end Record1252270103Finite
