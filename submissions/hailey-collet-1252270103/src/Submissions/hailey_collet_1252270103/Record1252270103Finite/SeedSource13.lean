/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource11
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource13 : Source := ⟨(248685498191/250000000000),(523530627991/125000000000),(18069292767/500000000000),(350876494821/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource13_valid : SeedSourceValid seedSource13 seedSource11 := by decide +kernel
#print axioms seedSource13_valid
end Record1252270103Finite
