/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.TopKernel
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.Top.Binding
open QRH.Cycle092.TopData QRH.PhysicalCertificate
noncomputable section

def actualRecords : List StoredLeaf := (forestRecords qForest).filter
  (fun leaf => leaf.route == .mixed)

theorem actualRecords_length : actualRecords.length=9681 := by decide +kernel

theorem mapped_take_append_drop {α β : Type*} (xs : List α) (f : α→β) (n : ℕ) :
    (xs.take n).map f ++ (xs.drop n).map f = xs.map f := by
  rw [←List.map_append,List.take_append_drop]

end
end QRH.Cycle092.Top.Binding
