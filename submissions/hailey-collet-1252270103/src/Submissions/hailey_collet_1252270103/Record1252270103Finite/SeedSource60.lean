/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource58
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource60 : Source := ⟨(193390518529/200000000000),(40860767569/12500000000),(54998999999/1000000000000),(564180496021/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource60_valid : SeedSourceValid seedSource60 seedSource58 := by decide +kernel
#print axioms seedSource60_valid
end Record1252270103Finite
