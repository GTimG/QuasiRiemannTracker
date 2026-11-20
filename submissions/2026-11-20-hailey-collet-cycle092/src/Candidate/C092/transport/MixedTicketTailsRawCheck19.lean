/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group19_raw0 : ((group19.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group19_raw1 : ((group19.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group19_raw2 : ((group19.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group19_raw3 : ((group19.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group19_raw4 : ((group19.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group19_raw5 : ((group19.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group19_raw6 : ((group19.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group19_raw_checked : group19.all rawBridgeCheck=true := by
  have he : group19 = ((group19.drop 0).take 50) ++ ((group19.drop 50).take 50) ++ ((group19.drop 100).take 50) ++ ((group19.drop 150).take 50) ++ ((group19.drop 200).take 50) ++ ((group19.drop 250).take 50) ++ ((group19.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group19_raw0,group19_raw1,group19_raw2,group19_raw3,group19_raw4,group19_raw5,group19_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
