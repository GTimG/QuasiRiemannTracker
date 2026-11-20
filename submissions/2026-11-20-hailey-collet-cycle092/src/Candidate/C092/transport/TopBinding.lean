/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.TopBinding00
import Candidate.C092.transport.TopBinding01
import Candidate.C092.transport.TopBinding02
import Candidate.C092.transport.TopBinding03
import Candidate.C092.transport.TopBinding04
import Candidate.C092.transport.TopBinding05
import Candidate.C092.transport.TopBinding06
import Candidate.C092.transport.TopBinding07
import Candidate.C092.transport.TopBinding08
import Candidate.C092.transport.TopBinding09
import Candidate.C092.transport.TopBinding10
import Candidate.C092.transport.TopBinding11
import Candidate.C092.transport.TopBinding12
import Candidate.C092.transport.TopBinding13
import Candidate.C092.transport.TopBinding14
import Candidate.C092.transport.TopBinding15
import Candidate.C092.transport.TopBinding16
import Candidate.C092.transport.TopBinding17
import Candidate.C092.transport.TopBinding18
import Candidate.C092.transport.TopBinding19
import Candidate.C092.transport.TopBinding20
import Candidate.C092.transport.TopBinding21
import Candidate.C092.transport.TopBinding22
import Candidate.C092.transport.TopBinding23
import Candidate.C092.transport.TopBinding24
import Candidate.C092.transport.TopBinding25
import Candidate.C092.transport.TopBinding26
import Candidate.C092.transport.TopBinding27
import Candidate.C092.transport.TopBinding28
import Candidate.C092.transport.TopBinding29
import Candidate.C092.transport.TopBinding30
import Candidate.C092.transport.TopBinding31

/-! Exact whole-forest binding assembled from bounded record-first box slices. -/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.Top.Binding
open QRH.Cycle092.TopData QRH.PhysicalCertificate
noncomputable section

theorem boxes_eq : rows.map Row.box = actualRecords.map StoredLeaf.box := by
  have hend : actualRecords.drop 9696=[] := by
    apply List.drop_eq_nil_of_le
    rw [actualRecords_length]
    omega
  have htail31 : TopData.group31.map Row.box = (actualRecords.drop 9393).map StoredLeaf.box := by
    refine group31_boxes.trans ?_
    have hm := mapped_take_append_drop (actualRecords.drop 9393) StoredLeaf.box 303
    simpa only [List.drop_drop,hend,List.map_nil,List.append_nil] using hm
  have htail30 : TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 9090).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group30_boxes htail31).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 9090) StoredLeaf.box 303
  have htail29 : TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 8787).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group29_boxes htail30).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 8787) StoredLeaf.box 303
  have htail28 : TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 8484).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group28_boxes htail29).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 8484) StoredLeaf.box 303
  have htail27 : TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 8181).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group27_boxes htail28).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 8181) StoredLeaf.box 303
  have htail26 : TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 7878).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group26_boxes htail27).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 7878) StoredLeaf.box 303
  have htail25 : TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 7575).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group25_boxes htail26).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 7575) StoredLeaf.box 303
  have htail24 : TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 7272).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group24_boxes htail25).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 7272) StoredLeaf.box 303
  have htail23 : TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 6969).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group23_boxes htail24).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 6969) StoredLeaf.box 303
  have htail22 : TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 6666).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group22_boxes htail23).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 6666) StoredLeaf.box 303
  have htail21 : TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 6363).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group21_boxes htail22).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 6363) StoredLeaf.box 303
  have htail20 : TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 6060).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group20_boxes htail21).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 6060) StoredLeaf.box 303
  have htail19 : TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 5757).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group19_boxes htail20).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 5757) StoredLeaf.box 303
  have htail18 : TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 5454).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group18_boxes htail19).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 5454) StoredLeaf.box 303
  have htail17 : TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 5151).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group17_boxes htail18).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 5151) StoredLeaf.box 303
  have htail16 : TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 4848).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group16_boxes htail17).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 4848) StoredLeaf.box 303
  have htail15 : TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 4545).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group15_boxes htail16).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 4545) StoredLeaf.box 303
  have htail14 : TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 4242).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group14_boxes htail15).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 4242) StoredLeaf.box 303
  have htail13 : TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 3939).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group13_boxes htail14).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 3939) StoredLeaf.box 303
  have htail12 : TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 3636).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group12_boxes htail13).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 3636) StoredLeaf.box 303
  have htail11 : TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 3333).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group11_boxes htail12).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 3333) StoredLeaf.box 303
  have htail10 : TopData.group10.map Row.box ++ TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 3030).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group10_boxes htail11).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 3030) StoredLeaf.box 303
  have htail09 : TopData.group09.map Row.box ++ TopData.group10.map Row.box ++ TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 2727).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group09_boxes htail10).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 2727) StoredLeaf.box 303
  have htail08 : TopData.group08.map Row.box ++ TopData.group09.map Row.box ++ TopData.group10.map Row.box ++ TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 2424).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group08_boxes htail09).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 2424) StoredLeaf.box 303
  have htail07 : TopData.group07.map Row.box ++ TopData.group08.map Row.box ++ TopData.group09.map Row.box ++ TopData.group10.map Row.box ++ TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 2121).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group07_boxes htail08).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 2121) StoredLeaf.box 303
  have htail06 : TopData.group06.map Row.box ++ TopData.group07.map Row.box ++ TopData.group08.map Row.box ++ TopData.group09.map Row.box ++ TopData.group10.map Row.box ++ TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 1818).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group06_boxes htail07).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 1818) StoredLeaf.box 303
  have htail05 : TopData.group05.map Row.box ++ TopData.group06.map Row.box ++ TopData.group07.map Row.box ++ TopData.group08.map Row.box ++ TopData.group09.map Row.box ++ TopData.group10.map Row.box ++ TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 1515).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group05_boxes htail06).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 1515) StoredLeaf.box 303
  have htail04 : TopData.group04.map Row.box ++ TopData.group05.map Row.box ++ TopData.group06.map Row.box ++ TopData.group07.map Row.box ++ TopData.group08.map Row.box ++ TopData.group09.map Row.box ++ TopData.group10.map Row.box ++ TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 1212).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group04_boxes htail05).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 1212) StoredLeaf.box 303
  have htail03 : TopData.group03.map Row.box ++ TopData.group04.map Row.box ++ TopData.group05.map Row.box ++ TopData.group06.map Row.box ++ TopData.group07.map Row.box ++ TopData.group08.map Row.box ++ TopData.group09.map Row.box ++ TopData.group10.map Row.box ++ TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 909).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group03_boxes htail04).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 909) StoredLeaf.box 303
  have htail02 : TopData.group02.map Row.box ++ TopData.group03.map Row.box ++ TopData.group04.map Row.box ++ TopData.group05.map Row.box ++ TopData.group06.map Row.box ++ TopData.group07.map Row.box ++ TopData.group08.map Row.box ++ TopData.group09.map Row.box ++ TopData.group10.map Row.box ++ TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 606).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group02_boxes htail03).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 606) StoredLeaf.box 303
  have htail01 : TopData.group01.map Row.box ++ TopData.group02.map Row.box ++ TopData.group03.map Row.box ++ TopData.group04.map Row.box ++ TopData.group05.map Row.box ++ TopData.group06.map Row.box ++ TopData.group07.map Row.box ++ TopData.group08.map Row.box ++ TopData.group09.map Row.box ++ TopData.group10.map Row.box ++ TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 303).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group01_boxes htail02).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 303) StoredLeaf.box 303
  have htail00 : TopData.group00.map Row.box ++ TopData.group01.map Row.box ++ TopData.group02.map Row.box ++ TopData.group03.map Row.box ++ TopData.group04.map Row.box ++ TopData.group05.map Row.box ++ TopData.group06.map Row.box ++ TopData.group07.map Row.box ++ TopData.group08.map Row.box ++ TopData.group09.map Row.box ++ TopData.group10.map Row.box ++ TopData.group11.map Row.box ++ TopData.group12.map Row.box ++ TopData.group13.map Row.box ++ TopData.group14.map Row.box ++ TopData.group15.map Row.box ++ TopData.group16.map Row.box ++ TopData.group17.map Row.box ++ TopData.group18.map Row.box ++ TopData.group19.map Row.box ++ TopData.group20.map Row.box ++ TopData.group21.map Row.box ++ TopData.group22.map Row.box ++ TopData.group23.map Row.box ++ TopData.group24.map Row.box ++ TopData.group25.map Row.box ++ TopData.group26.map Row.box ++ TopData.group27.map Row.box ++ TopData.group28.map Row.box ++ TopData.group29.map Row.box ++ TopData.group30.map Row.box ++ TopData.group31.map Row.box = (actualRecords.drop 0).map StoredLeaf.box := by
    refine (congrArg₂ (fun a b : List QRH.Coverage.Box => a++b) group00_boxes htail01).trans ?_
    simpa only [List.drop_drop] using mapped_take_append_drop (actualRecords.drop 0) StoredLeaf.box 303
  simpa only [rows,List.map_append,List.drop_zero] using htail00

end
end QRH.Cycle092.Top.Binding
#print axioms QRH.Cycle092.Top.Binding.boxes_eq
