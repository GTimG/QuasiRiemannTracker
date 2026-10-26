/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source244
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source259
set_option autoImplicit false
namespace Record1252270103Finite
def source263 : Source := ⟨(193670740919/200000000000),(2638046061/800000000),(549989/10000000),(283792100789/500000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source263_valid : SourceValid source263 source259 (some source244) := by decide +kernel
#print axioms source263_valid
end Record1252270103Finite
