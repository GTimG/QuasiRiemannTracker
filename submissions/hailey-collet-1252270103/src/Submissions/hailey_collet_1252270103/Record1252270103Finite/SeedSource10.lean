/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource08
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource10 : Source := ⟨(993898618067/1000000000000),(207430500233/50000000000),(37010817529/1000000000000),(696148985463/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource10_valid : SeedSourceValid seedSource10 seedSource08 := by decide +kernel
#print axioms seedSource10_valid
end Record1252270103Finite
