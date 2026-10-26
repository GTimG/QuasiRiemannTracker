/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource37
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource39 : Source := ⟨(984023104139/1000000000000),(469837010403/125000000000),(45919661693/1000000000000),(637142847271/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource39_valid : SeedSourceValid seedSource39 seedSource37 := by decide +kernel
#print axioms seedSource39_valid
end Record1252270103Finite
