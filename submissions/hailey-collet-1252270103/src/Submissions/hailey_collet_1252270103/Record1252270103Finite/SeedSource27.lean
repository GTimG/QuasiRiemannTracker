/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource25
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource27 : Source := ⟨(989406842387/1000000000000),(3955032836539/1000000000000),(20749212491/500000000000),(333375612991/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource27_valid : SeedSourceValid seedSource27 seedSource25 := by decide +kernel
#print axioms seedSource27_valid
end Record1252270103Finite
