/- The first parent of the chain: Sil's fourth-power source face (upstream PR 74,
`sil-fourth-power-20261025`, Apache-2.0), as a node of Collet's finite source graph. Its source
theorem is in `Graph/Start.lean`; this module only names the face, so that the step certificates do
not depend on the source construction. -/
import Submissions.hailey_collet_1252270103.Record1252270103Graph.GraphContract
set_option autoImplicit false
namespace QRH.RepeatedMarks
open Record1252270103Finite

/-- `GlobalSource (99999/100000) (93/25) (3/50)`, with the fees of Collet's natural node. -/
def start : Source := ⟨99999/100000,93/25,3/50,0,1/10^12,1/10^8,1/10^7⟩

theorem start_good : QRH.Record1252270103Graph.ParentGood start := by
  norm_num [QRH.Record1252270103Graph.ParentGood, start]

end QRH.RepeatedMarks
