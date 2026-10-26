/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource36
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource38 : Source := ⟨(979976585481/1000000000000),(3629051065709/1000000000000),(4878594477/100000000000),(617602569731/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource38_valid : SeedSourceValid seedSource38 seedSource36 := by decide +kernel
#print axioms seedSource38_valid
end Record1252270103Finite
