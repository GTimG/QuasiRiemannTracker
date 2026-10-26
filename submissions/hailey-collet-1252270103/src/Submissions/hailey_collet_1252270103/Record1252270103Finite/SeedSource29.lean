/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource27
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource29 : Source := ⟨(9887529443/10000000000),(982344822523/250000000000),(42119111023/1000000000000),(165648891143/250000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource29_valid : SeedSourceValid seedSource29 seedSource27 := by decide +kernel
#print axioms seedSource29_valid
end Record1252270103Finite
