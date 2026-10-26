/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource52
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource54 : Source := ⟨(194205834697/200000000000),(105421617533/31250000000),(27163344067/500000000000),(579503754483/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource54_valid : SeedSourceValid seedSource54 seedSource52 := by decide +kernel
#print axioms seedSource54_valid
end Record1252270103Finite
