/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource19
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource21 : Source := ⟨(991675436417/1000000000000),(253008442941/62500000000),(39365150407/1000000000000),(42550950461/62500000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource21_valid : SeedSourceValid seedSource21 seedSource19 := by decide +kernel
#print axioms seedSource21_valid
end Record1252270103Finite
