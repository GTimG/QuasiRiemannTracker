/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source255
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source272
set_option autoImplicit false
namespace Record1252270103Finite
def source275 : Source := ⟨(6017117169/6250000000),(3159434155041/1000000000000),(549989/10000000),(273490161317/500000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source275_valid : SourceValid source275 source272 (some source255) := by decide +kernel
#print axioms source275_valid
end Record1252270103Finite
