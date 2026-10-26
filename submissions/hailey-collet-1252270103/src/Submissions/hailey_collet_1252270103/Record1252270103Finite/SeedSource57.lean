/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource55
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource57 : Source := ⟨(7602112167/7812500000),(214229376577/62500000000),(13287688631/250000000000),(587700845567/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource57_valid : SeedSourceValid seedSource57 seedSource55 := by decide +kernel
#print axioms seedSource57_valid
end Record1252270103Finite
