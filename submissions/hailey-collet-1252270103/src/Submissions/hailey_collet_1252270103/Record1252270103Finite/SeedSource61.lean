/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource59
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource61 : Source := ⟨(485243547489/500000000000),(3358580552439/1000000000000),(54635093269/1000000000000),(577434117401/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource61_valid : SeedSourceValid seedSource61 seedSource59 := by decide +kernel
#print axioms seedSource61_valid
end Record1252270103Finite
