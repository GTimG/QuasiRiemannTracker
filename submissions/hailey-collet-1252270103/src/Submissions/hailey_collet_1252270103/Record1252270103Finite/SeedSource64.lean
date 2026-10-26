/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource62
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource64 : Source := ⟨(482045093689/500000000000),(3198839752287/1000000000000),(54998999999/1000000000000),(553741151397/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource64_valid : SeedSourceValid seedSource64 seedSource62 := by decide +kernel
#print axioms seedSource64_valid
end Record1252270103Finite
