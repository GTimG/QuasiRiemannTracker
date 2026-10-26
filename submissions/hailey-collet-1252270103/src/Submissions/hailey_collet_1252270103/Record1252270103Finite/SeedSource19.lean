/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource17
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource19 : Source := ⟨(992932619959/1000000000000),(2051514332977/500000000000),(38138921239/1000000000000),(688794396301/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource19_valid : SeedSourceValid seedSource19 seedSource17 := by decide +kernel
#print axioms seedSource19_valid
end Record1252270103Finite
