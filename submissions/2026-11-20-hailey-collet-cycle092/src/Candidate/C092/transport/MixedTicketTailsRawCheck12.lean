/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group12_raw0 : ((group12.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group12_raw1 : ((group12.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group12_raw2 : ((group12.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group12_raw3 : ((group12.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group12_raw4 : ((group12.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group12_raw5 : ((group12.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group12_raw6 : ((group12.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group12_raw_checked : group12.all rawBridgeCheck=true := by
  have he : group12 = ((group12.drop 0).take 50) ++ ((group12.drop 50).take 50) ++ ((group12.drop 100).take 50) ++ ((group12.drop 150).take 50) ++ ((group12.drop 200).take 50) ++ ((group12.drop 250).take 50) ++ ((group12.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group12_raw0,group12_raw1,group12_raw2,group12_raw3,group12_raw4,group12_raw5,group12_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
