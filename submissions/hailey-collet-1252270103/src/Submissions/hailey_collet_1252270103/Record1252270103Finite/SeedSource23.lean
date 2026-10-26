/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource21
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource23 : Source := ⟨(991076914713/1000000000000),(502831635059/125000000000),(9996711513/250000000000),(338350929929/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource23_valid : SeedSourceValid seedSource23 seedSource21 := by decide +kernel
#print axioms seedSource23_valid
end Record1252270103Finite
