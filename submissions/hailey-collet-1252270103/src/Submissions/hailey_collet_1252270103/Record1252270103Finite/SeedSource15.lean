/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource13
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource15 : Source := ⟨(993683145537/1000000000000),(4137770984837/1000000000000),(7456496227/200000000000),(347197111783/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource15_valid : SeedSourceValid seedSource15 seedSource13 := by decide +kernel
#print axioms seedSource15_valid
end Record1252270103Finite
