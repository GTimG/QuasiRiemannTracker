/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource53
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource55 : Source := ⟨(487245121791/500000000000),(108338842211/31250000000),(52322908519/1000000000000),(18543427599/31250000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource55_valid : SeedSourceValid seedSource55 seedSource53 := by decide +kernel
#print axioms seedSource55_valid
end Record1252270103Finite
