/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source145
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source206
set_option autoImplicit false
namespace Record1252270103Finite
def source222 : Source := ⟨(484709614911/500000000000),(3325007191901/1000000000000),(549989/10000000),(285836545169/500000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source222_valid : SourceValid source222 source206 (some source145) := by decide +kernel
#print axioms source222_valid
end Record1252270103Finite
