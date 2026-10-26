/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource26
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource28 : Source := ⟨(492202170349/500000000000),(754665390681/200000000000),(45556254073/1000000000000),(127915292131/200000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource28_valid : SeedSourceValid seedSource28 seedSource26 := by decide +kernel
#print axioms seedSource28_valid
end Record1252270103Finite
