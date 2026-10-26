/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource41
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource43 : Source := ⟨(981183111871/1000000000000),(146635426311/40000000000),(11990792159/250000000000),(311642043311/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource43_valid : SeedSourceValid seedSource43 seedSource41 := by decide +kernel
#print axioms seedSource43_valid
end Record1252270103Finite
