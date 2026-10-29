/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.FinalEnvelopeBounds
import Candidate.Local.Qrh.JointDetector.ReturnCoverCommands
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part00
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part01
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part02
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part03
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part04
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part05
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part06
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part07
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part08
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part09
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part10
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part11
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part12
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part13
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part14
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part15
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part16
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part17
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part18
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part19
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part20
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part21
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part22
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part23
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part24
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part25
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part26
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part27
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part28
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part29
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part30
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part31
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part32
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part33
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part34
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part35
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part36
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part37
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part38
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part39
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part40
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part41
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part42
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part43
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part44
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part45
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part46
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part47
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part48
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part49
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part50
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part51
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part52
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part53
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part54
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part55
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Rows.Part56
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.BoundarySeedReturn.FinalEdges
open QRH.Record1252270103Return
noncomputable section
set_option maxRecDepth 8192
abbrev ReturnAt (e : Edge) (δ p : ℝ) : Prop := Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve
theorem window01_mem : returnWindow01 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[0]? = some returnWindow01)
theorem window02_mem : returnWindow02 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[1]? = some returnWindow02)
theorem window03_mem : returnWindow03 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[2]? = some returnWindow03)
theorem window04_mem : returnWindow04 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[3]? = some returnWindow04)
theorem window05_mem : returnWindow05 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[4]? = some returnWindow05)
theorem window06_mem : returnWindow06 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[5]? = some returnWindow06)
theorem window07_mem : returnWindow07 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[6]? = some returnWindow07)
theorem window08_mem : returnWindow08 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[7]? = some returnWindow08)
theorem window09_mem : returnWindow09 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[8]? = some returnWindow09)
theorem window10_mem : returnWindow10 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[9]? = some returnWindow10)
theorem window11_mem : returnWindow11 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[10]? = some returnWindow11)
theorem window12_mem : returnWindow12 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[11]? = some returnWindow12)
theorem window13_mem : returnWindow13 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[12]? = some returnWindow13)
theorem window14_mem : returnWindow14 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[13]? = some returnWindow14)
theorem window15_mem : returnWindow15 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[14]? = some returnWindow15)
theorem window16_mem : returnWindow16 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[15]? = some returnWindow16)
theorem window17_mem : returnWindow17 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[16]? = some returnWindow17)
theorem window18_mem : returnWindow18 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[17]? = some returnWindow18)
theorem window19_mem : returnWindow19 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[18]? = some returnWindow19)
theorem window20_mem : returnWindow20 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[19]? = some returnWindow20)
theorem window21_mem : returnWindow21 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[20]? = some returnWindow21)
theorem window22_mem : returnWindow22 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[21]? = some returnWindow22)
theorem window23_mem : returnWindow23 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[22]? = some returnWindow23)
theorem window24_mem : returnWindow24 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[23]? = some returnWindow24)
theorem window25_mem : returnWindow25 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[24]? = some returnWindow25)
theorem window26_mem : returnWindow26 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[25]? = some returnWindow26)
theorem window27_mem : returnWindow27 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[26]? = some returnWindow27)
theorem window28_mem : returnWindow28 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[27]? = some returnWindow28)
theorem window29_mem : returnWindow29 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[28]? = some returnWindow29)
theorem window30_mem : returnWindow30 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[29]? = some returnWindow30)
theorem window31_mem : returnWindow31 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[30]? = some returnWindow31)
theorem window32_mem : returnWindow32 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[31]? = some returnWindow32)
theorem window33_mem : returnWindow33 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[32]? = some returnWindow33)
theorem window34_mem : returnWindow34 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[33]? = some returnWindow34)
theorem window35_mem : returnWindow35 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[34]? = some returnWindow35)
theorem window36_mem : returnWindow36 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[35]? = some returnWindow36)
theorem window37_mem : returnWindow37 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[36]? = some returnWindow37)
theorem window38_mem : returnWindow38 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[37]? = some returnWindow38)
theorem window39_mem : returnWindow39 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[38]? = some returnWindow39)
theorem window40_mem : returnWindow40 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[39]? = some returnWindow40)
theorem window41_mem : returnWindow41 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[40]? = some returnWindow41)
theorem window42_mem : returnWindow42 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[41]? = some returnWindow42)
theorem window43_mem : returnWindow43 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[42]? = some returnWindow43)
theorem window44_mem : returnWindow44 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[43]? = some returnWindow44)
theorem window45_mem : returnWindow45 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[44]? = some returnWindow45)
theorem window46_mem : returnWindow46 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[45]? = some returnWindow46)
theorem window47_mem : returnWindow47 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[46]? = some returnWindow47)
theorem window48_mem : returnWindow48 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[47]? = some returnWindow48)
theorem window49_mem : returnWindow49 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[48]? = some returnWindow49)
theorem window50_mem : returnWindow50 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[49]? = some returnWindow50)
theorem window51_mem : returnWindow51 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[50]? = some returnWindow51)
theorem window52_mem : returnWindow52 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[51]? = some returnWindow52)
theorem window53_mem : returnWindow53 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[52]? = some returnWindow53)
theorem window54_mem : returnWindow54 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[53]? = some returnWindow54)
theorem window55_mem : returnWindow55 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[54]? = some returnWindow55)
theorem window56_mem : returnWindow56 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[55]? = some returnWindow56)
theorem window57_mem : returnWindow57 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[56]? = some returnWindow57)
theorem window58_mem : returnWindow58 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[57]? = some returnWindow58)
theorem window59_mem : returnWindow59 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[58]? = some returnWindow59)
theorem window60_mem : returnWindow60 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[59]? = some returnWindow60)
theorem window61_mem : returnWindow61 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[60]? = some returnWindow61)
theorem window62_mem : returnWindow62 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[61]? = some returnWindow62)
theorem window63_mem : returnWindow63 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[62]? = some returnWindow63)
theorem window64_mem : returnWindow64 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[63]? = some returnWindow64)
theorem window65_mem : returnWindow65 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[64]? = some returnWindow65)
theorem window66_mem : returnWindow66 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[65]? = some returnWindow66)
theorem window67_mem : returnWindow67 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[66]? = some returnWindow67)
theorem window68_mem : returnWindow68 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[67]? = some returnWindow68)
theorem window69_mem : returnWindow69 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[68]? = some returnWindow69)
theorem window70_mem : returnWindow70 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[69]? = some returnWindow70)
theorem window71_mem : returnWindow71 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[70]? = some returnWindow71)
theorem window72_mem : returnWindow72 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[71]? = some returnWindow72)
theorem window73_mem : returnWindow73 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[72]? = some returnWindow73)
theorem window74_mem : returnWindow74 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[73]? = some returnWindow74)
theorem window75_mem : returnWindow75 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[74]? = some returnWindow75)
theorem window76_mem : returnWindow76 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[75]? = some returnWindow76)
theorem window77_mem : returnWindow77 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[76]? = some returnWindow77)
theorem window78_mem : returnWindow78 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[77]? = some returnWindow78)
theorem window79_mem : returnWindow79 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[78]? = some returnWindow79)
theorem window80_mem : returnWindow80 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[79]? = some returnWindow80)
theorem window81_mem : returnWindow81 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[80]? = some returnWindow81)
theorem window82_mem : returnWindow82 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[81]? = some returnWindow82)
theorem window83_mem : returnWindow83 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[82]? = some returnWindow83)
theorem window84_mem : returnWindow84 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[83]? = some returnWindow84)
theorem window85_mem : returnWindow85 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[84]? = some returnWindow85)
theorem window86_mem : returnWindow86 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[85]? = some returnWindow86)
theorem window87_mem : returnWindow87 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[86]? = some returnWindow87)
theorem window88_mem : returnWindow88 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[87]? = some returnWindow88)
theorem window89_mem : returnWindow89 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[88]? = some returnWindow89)
theorem window90_mem : returnWindow90 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[89]? = some returnWindow90)
theorem window91_mem : returnWindow91 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[90]? = some returnWindow91)
theorem window92_mem : returnWindow92 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[91]? = some returnWindow92)
theorem window93_mem : returnWindow93 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[92]? = some returnWindow93)
theorem window94_mem : returnWindow94 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[93]? = some returnWindow94)
theorem window95_mem : returnWindow95 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[94]? = some returnWindow95)
theorem window96_mem : returnWindow96 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[95]? = some returnWindow96)
theorem window97_mem : returnWindow97 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[96]? = some returnWindow97)
theorem window98_mem : returnWindow98 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[97]? = some returnWindow98)
theorem window99_mem : returnWindow99 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[98]? = some returnWindow99)
theorem window100_mem : returnWindow100 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[99]? = some returnWindow100)
theorem window101_mem : returnWindow101 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[100]? = some returnWindow101)
theorem window102_mem : returnWindow102 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[101]? = some returnWindow102)
theorem window103_mem : returnWindow103 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[102]? = some returnWindow103)
theorem window104_mem : returnWindow104 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[103]? = some returnWindow104)
theorem window105_mem : returnWindow105 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[104]? = some returnWindow105)
theorem window106_mem : returnWindow106 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[105]? = some returnWindow106)
theorem window107_mem : returnWindow107 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[106]? = some returnWindow107)
theorem window108_mem : returnWindow108 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[107]? = some returnWindow108)
theorem window109_mem : returnWindow109 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[108]? = some returnWindow109)
theorem window110_mem : returnWindow110 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[109]? = some returnWindow110)
theorem window111_mem : returnWindow111 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[110]? = some returnWindow111)
theorem window112_mem : returnWindow112 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[111]? = some returnWindow112)
theorem window113_mem : returnWindow113 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[112]? = some returnWindow113)
theorem window114_mem : returnWindow114 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[113]? = some returnWindow114)
theorem window115_mem : returnWindow115 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[114]? = some returnWindow115)
theorem window116_mem : returnWindow116 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[115]? = some returnWindow116)
theorem window117_mem : returnWindow117 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[116]? = some returnWindow117)
theorem window118_mem : returnWindow118 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[117]? = some returnWindow118)
theorem window119_mem : returnWindow119 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[118]? = some returnWindow119)
theorem window120_mem : returnWindow120 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[119]? = some returnWindow120)
theorem window121_mem : returnWindow121 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[120]? = some returnWindow121)
theorem window122_mem : returnWindow122 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[121]? = some returnWindow122)
theorem window123_mem : returnWindow123 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[122]? = some returnWindow123)
theorem window124_mem : returnWindow124 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[123]? = some returnWindow124)
theorem window125_mem : returnWindow125 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[124]? = some returnWindow125)
theorem window126_mem : returnWindow126 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[125]? = some returnWindow126)
theorem window127_mem : returnWindow127 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[126]? = some returnWindow127)
theorem window128_mem : returnWindow128 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[127]? = some returnWindow128)
theorem window129_mem : returnWindow129 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[128]? = some returnWindow129)
theorem window130_mem : returnWindow130 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[129]? = some returnWindow130)
theorem window131_mem : returnWindow131 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[130]? = some returnWindow131)
theorem window132_mem : returnWindow132 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[131]? = some returnWindow132)
theorem window133_mem : returnWindow133 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[132]? = some returnWindow133)
theorem window134_mem : returnWindow134 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[133]? = some returnWindow134)
theorem window135_mem : returnWindow135 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[134]? = some returnWindow135)
theorem window136_mem : returnWindow136 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[135]? = some returnWindow136)
theorem window137_mem : returnWindow137 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[136]? = some returnWindow137)
theorem window138_mem : returnWindow138 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[137]? = some returnWindow138)
theorem window139_mem : returnWindow139 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[138]? = some returnWindow139)
theorem window140_mem : returnWindow140 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[139]? = some returnWindow140)
theorem window141_mem : returnWindow141 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[140]? = some returnWindow141)
theorem window142_mem : returnWindow142 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[141]? = some returnWindow142)
theorem window143_mem : returnWindow143 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[142]? = some returnWindow143)
theorem window144_mem : returnWindow144 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[143]? = some returnWindow144)
theorem window145_mem : returnWindow145 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[144]? = some returnWindow145)
theorem window146_mem : returnWindow146 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[145]? = some returnWindow146)
theorem window147_mem : returnWindow147 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[146]? = some returnWindow147)
theorem window148_mem : returnWindow148 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[147]? = some returnWindow148)
theorem window149_mem : returnWindow149 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[148]? = some returnWindow149)
theorem window150_mem : returnWindow150 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[149]? = some returnWindow150)
theorem window151_mem : returnWindow151 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[150]? = some returnWindow151)
theorem window152_mem : returnWindow152 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[151]? = some returnWindow152)
theorem window153_mem : returnWindow153 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[152]? = some returnWindow153)
theorem window154_mem : returnWindow154 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[153]? = some returnWindow154)
theorem window155_mem : returnWindow155 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[154]? = some returnWindow155)
theorem window156_mem : returnWindow156 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[155]? = some returnWindow156)
theorem window157_mem : returnWindow157 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[156]? = some returnWindow157)
theorem window158_mem : returnWindow158 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[157]? = some returnWindow158)
theorem window159_mem : returnWindow159 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[158]? = some returnWindow159)
theorem window160_mem : returnWindow160 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[159]? = some returnWindow160)
theorem window161_mem : returnWindow161 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[160]? = some returnWindow161)
theorem window162_mem : returnWindow162 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[161]? = some returnWindow162)
theorem window163_mem : returnWindow163 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[162]? = some returnWindow163)
theorem window164_mem : returnWindow164 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[163]? = some returnWindow164)
theorem window165_mem : returnWindow165 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[164]? = some returnWindow165)
theorem window166_mem : returnWindow166 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[165]? = some returnWindow166)
theorem window167_mem : returnWindow167 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[166]? = some returnWindow167)
theorem window168_mem : returnWindow168 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[167]? = some returnWindow168)
theorem window169_mem : returnWindow169 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[168]? = some returnWindow169)
theorem window170_mem : returnWindow170 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[169]? = some returnWindow170)
theorem window171_mem : returnWindow171 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[170]? = some returnWindow171)
theorem window172_mem : returnWindow172 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[171]? = some returnWindow172)
theorem window173_mem : returnWindow173 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[172]? = some returnWindow173)
theorem window174_mem : returnWindow174 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[173]? = some returnWindow174)
theorem window175_mem : returnWindow175 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[174]? = some returnWindow175)
theorem window176_mem : returnWindow176 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[175]? = some returnWindow176)
theorem window177_mem : returnWindow177 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[176]? = some returnWindow177)
theorem window178_mem : returnWindow178 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[177]? = some returnWindow178)
theorem window179_mem : returnWindow179 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[178]? = some returnWindow179)
theorem window180_mem : returnWindow180 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[179]? = some returnWindow180)
theorem window181_mem : returnWindow181 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[180]? = some returnWindow181)
theorem window182_mem : returnWindow182 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[181]? = some returnWindow182)
theorem window183_mem : returnWindow183 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[182]? = some returnWindow183)
theorem window184_mem : returnWindow184 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[183]? = some returnWindow184)
theorem window185_mem : returnWindow185 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[184]? = some returnWindow185)
theorem window186_mem : returnWindow186 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[185]? = some returnWindow186)
theorem window187_mem : returnWindow187 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[186]? = some returnWindow187)
theorem window188_mem : returnWindow188 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[187]? = some returnWindow188)
theorem window189_mem : returnWindow189 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[188]? = some returnWindow189)
theorem window190_mem : returnWindow190 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[189]? = some returnWindow190)
theorem window191_mem : returnWindow191 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[190]? = some returnWindow191)
theorem window192_mem : returnWindow192 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[191]? = some returnWindow192)
theorem window193_mem : returnWindow193 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[192]? = some returnWindow193)
theorem window194_mem : returnWindow194 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[193]? = some returnWindow194)
theorem window195_mem : returnWindow195 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[194]? = some returnWindow195)
theorem window196_mem : returnWindow196 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[195]? = some returnWindow196)
theorem window197_mem : returnWindow197 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[196]? = some returnWindow197)
theorem window198_mem : returnWindow198 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[197]? = some returnWindow198)
theorem window199_mem : returnWindow199 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[198]? = some returnWindow199)
theorem window200_mem : returnWindow200 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[199]? = some returnWindow200)
theorem window201_mem : returnWindow201 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[200]? = some returnWindow201)
theorem window202_mem : returnWindow202 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[201]? = some returnWindow202)
theorem window203_mem : returnWindow203 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[202]? = some returnWindow203)
theorem window204_mem : returnWindow204 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[203]? = some returnWindow204)
theorem window205_mem : returnWindow205 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[204]? = some returnWindow205)
theorem window206_mem : returnWindow206 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[205]? = some returnWindow206)
theorem window207_mem : returnWindow207 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[206]? = some returnWindow207)
theorem window208_mem : returnWindow208 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[207]? = some returnWindow208)
theorem window209_mem : returnWindow209 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[208]? = some returnWindow209)
theorem window210_mem : returnWindow210 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[209]? = some returnWindow210)
theorem window211_mem : returnWindow211 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[210]? = some returnWindow211)
theorem window212_mem : returnWindow212 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[211]? = some returnWindow212)
theorem window213_mem : returnWindow213 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[212]? = some returnWindow213)
theorem window214_mem : returnWindow214 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[213]? = some returnWindow214)
theorem window215_mem : returnWindow215 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[214]? = some returnWindow215)
theorem window216_mem : returnWindow216 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[215]? = some returnWindow216)
theorem window217_mem : returnWindow217 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[216]? = some returnWindow217)
theorem window218_mem : returnWindow218 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[217]? = some returnWindow218)
theorem window219_mem : returnWindow219 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[218]? = some returnWindow219)
theorem window220_mem : returnWindow220 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[219]? = some returnWindow220)
theorem window221_mem : returnWindow221 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[220]? = some returnWindow221)
theorem window222_mem : returnWindow222 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[221]? = some returnWindow222)
theorem window223_mem : returnWindow223 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[222]? = some returnWindow223)
theorem window224_mem : returnWindow224 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[223]? = some returnWindow224)
theorem window225_mem : returnWindow225 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[224]? = some returnWindow225)
theorem window226_mem : returnWindow226 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[225]? = some returnWindow226)
theorem window227_mem : returnWindow227 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[226]? = some returnWindow227)
theorem window228_mem : returnWindow228 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[227]? = some returnWindow228)
theorem window229_mem : returnWindow229 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[228]? = some returnWindow229)
theorem window230_mem : returnWindow230 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[229]? = some returnWindow230)
theorem window231_mem : returnWindow231 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[230]? = some returnWindow231)
theorem window232_mem : returnWindow232 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[231]? = some returnWindow232)
theorem window233_mem : returnWindow233 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[232]? = some returnWindow233)
theorem window234_mem : returnWindow234 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[233]? = some returnWindow234)
theorem window235_mem : returnWindow235 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[234]? = some returnWindow235)
theorem window236_mem : returnWindow236 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[235]? = some returnWindow236)
theorem window237_mem : returnWindow237 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[236]? = some returnWindow237)
theorem window238_mem : returnWindow238 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[237]? = some returnWindow238)
theorem window239_mem : returnWindow239 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[238]? = some returnWindow239)
theorem window240_mem : returnWindow240 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[239]? = some returnWindow240)
theorem window241_mem : returnWindow241 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[240]? = some returnWindow241)
theorem window242_mem : returnWindow242 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[241]? = some returnWindow242)
theorem window243_mem : returnWindow243 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[242]? = some returnWindow243)
theorem window244_mem : returnWindow244 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[243]? = some returnWindow244)
theorem window245_mem : returnWindow245 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[244]? = some returnWindow245)
theorem window246_mem : returnWindow246 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[245]? = some returnWindow246)
theorem window247_mem : returnWindow247 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[246]? = some returnWindow247)
theorem window248_mem : returnWindow248 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[247]? = some returnWindow248)
theorem window249_mem : returnWindow249 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[248]? = some returnWindow249)
theorem window250_mem : returnWindow250 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[249]? = some returnWindow250)
theorem window251_mem : returnWindow251 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[250]? = some returnWindow251)
theorem window252_mem : returnWindow252 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[251]? = some returnWindow252)
theorem window253_mem : returnWindow253 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[252]? = some returnWindow253)
theorem window254_mem : returnWindow254 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[253]? = some returnWindow254)
theorem window255_mem : returnWindow255 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[254]? = some returnWindow255)
theorem window256_mem : returnWindow256 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[255]? = some returnWindow256)
theorem window257_mem : returnWindow257 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[256]? = some returnWindow257)
theorem window258_mem : returnWindow258 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[257]? = some returnWindow258)
theorem window259_mem : returnWindow259 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[258]? = some returnWindow259)
theorem window260_mem : returnWindow260 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[259]? = some returnWindow260)
theorem window261_mem : returnWindow261 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[260]? = some returnWindow261)
theorem window262_mem : returnWindow262 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[261]? = some returnWindow262)
theorem window263_mem : returnWindow263 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[262]? = some returnWindow263)
theorem window264_mem : returnWindow264 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[263]? = some returnWindow264)
theorem window265_mem : returnWindow265 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[264]? = some returnWindow265)
theorem window266_mem : returnWindow266 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[265]? = some returnWindow266)
theorem window267_mem : returnWindow267 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[266]? = some returnWindow267)
theorem window268_mem : returnWindow268 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[267]? = some returnWindow268)
theorem window269_mem : returnWindow269 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[268]? = some returnWindow269)
theorem window270_mem : returnWindow270 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[269]? = some returnWindow270)
theorem window271_mem : returnWindow271 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[270]? = some returnWindow271)
theorem window272_mem : returnWindow272 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[271]? = some returnWindow272)
theorem window273_mem : returnWindow273 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[272]? = some returnWindow273)
theorem window274_mem : returnWindow274 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[273]? = some returnWindow274)
theorem window275_mem : returnWindow275 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[274]? = some returnWindow275)
theorem window276_mem : returnWindow276 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[275]? = some returnWindow276)
theorem window277_mem : returnWindow277 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[276]? = some returnWindow277)
theorem window278_mem : returnWindow278 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[277]? = some returnWindow278)
theorem window279_mem : returnWindow279 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[278]? = some returnWindow279)
theorem window280_mem : returnWindow280 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[279]? = some returnWindow280)
theorem window281_mem : returnWindow281 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[280]? = some returnWindow281)
theorem window282_mem : returnWindow282 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[281]? = some returnWindow282)
theorem window283_mem : returnWindow283 ∈ returnWindows := by exact List.mem_of_getElem? (by rfl : returnWindows[282]? = some returnWindow283)

theorem envelope_row000 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row000_pos at_branch .old

theorem envelope_row001 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row001_pos at_branch .old

theorem envelope_row002 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row002_pos at_branch .old

theorem envelope_row003 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row003_pos at_branch .old

theorem envelope_row004 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row004_pos at_branch .old

theorem envelope_row005 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row005_pos at_branch .old

theorem envelope_row006 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row006_pos at_branch .old

theorem envelope_row007 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row007_pos at_branch .old

theorem envelope_row008 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row008_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row009 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row009_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row010 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row010_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row011 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row011_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row012 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row012_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row013 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row013_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row014 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row014_pos at_branch .old

theorem envelope_row015 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row015_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row016 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row016_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row017 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row017_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row018 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row018_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row019 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row019_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row020 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row020_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row021 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row021_pos at_branch .old

theorem envelope_row022 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row022_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row023 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row023_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row024 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row024_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row025 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row025_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row026 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row026_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row027 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row027_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row028 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row028_pos at_branch .old

theorem envelope_row029 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row029_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row030 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row030_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row031 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row031_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row032 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row032_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row033 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row033_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row034 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row034_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row035 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row035_pos at_branch .old

theorem envelope_row036 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row036_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row037 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row037_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row038 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row038_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row039 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row039_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row040 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row040_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row041 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row041_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row042 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row042_pos at_branch .old

theorem envelope_row043 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row043_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row044 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row044_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row045 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row045_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row046 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row046_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row047 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row047_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row048 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row048_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row049 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row049_pos at_branch .old

theorem envelope_row050 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row050_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row051 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row051_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row052 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row052_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row053 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row053_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row054 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row054_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row055 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row055_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row056 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row056_pos at_branch .old

theorem envelope_row057 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row057_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row058 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row058_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row059 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row059_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row060 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row060_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row061 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row061_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row062 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row062_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row063 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row063_pos at_branch .old

theorem envelope_row064 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row064_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row065 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row065_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row066 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row066_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row067 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row067_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row068 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row068_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row069 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row069_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row070 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row070_pos at_branch .old

theorem envelope_row071 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row071_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row072 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row072_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row073 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row073_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row074 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row074_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row075 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row075_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row076 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row076_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row077 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row077_pos at_branch .old

theorem envelope_row078 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row078_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row079 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row079_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row080 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row080_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row081 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row081_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row082 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row082_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row083 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row083_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row084 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row084_pos at_branch .old

theorem envelope_row085 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row085_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row086 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row086_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row087 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row087_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row088 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row088_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row089 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row089_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row090 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row090_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row091 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row091_pos at_branch .old

theorem envelope_row092 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row092_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row093 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row093_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row094 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row094_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row095 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row095_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row096 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row096_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row097 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row097_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row098 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row098_pos at_branch .old

theorem envelope_row099 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row099_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row100 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row100_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row101 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row101_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row102 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row102_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row103 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row103_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row104 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row104_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row105 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row105_pos at_branch .old

theorem envelope_row106 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row106_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row107 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row107_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row108 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row108_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row109 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row109_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row110 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row110_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row111 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row111_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row112 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row112_pos at_branch .old

theorem envelope_row113 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row113_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row114 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row114_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row115 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row115_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row116 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row116_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row117 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row117_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row118 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row118_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row119 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row119_pos at_branch .old

theorem envelope_row120 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row120_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row121 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row121_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row122 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row122_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row123 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row123_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row124 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row124_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row125 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row125_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row126 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row126_pos at_branch .old

theorem envelope_row127 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row127_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row128 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row128_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row129 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row129_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row130 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row130_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row131 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row131_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row132 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row132_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row133 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row133_pos at_branch .old

theorem envelope_row134 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row134_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row135 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row135_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row136 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row136_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row137 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row137_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row138 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row138_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row139 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row139_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row140 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row140_pos at_branch .old

theorem envelope_row141 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row141_pos at_branch .Pwide at_window returnWindow90 with_member window90_mem box((51/128:ℝ),(13/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row142 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row142_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row143 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row143_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row144 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row144_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row145 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row145_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row146 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row146_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row147 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row147_pos at_branch .old

theorem envelope_row148 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row148_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row149 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row149_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row150 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row150_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row151 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row151_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row152 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row152_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row153 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row153_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row154 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row154_pos at_branch .old

theorem envelope_row155 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row155_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row156 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row156_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row157 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row157_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row158 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row158_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row159 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row159_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row160 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row160_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row161 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row161_pos at_branch .old

theorem envelope_row162 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row162_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row163 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row163_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row164 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row164_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row165 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row165_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row166 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row166_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row167 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row167_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row168 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row168_pos at_branch .old

theorem envelope_row169 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row169_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row170 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row170_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row171 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row171_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row172 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row172_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row173 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row173_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row174 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row174_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row175 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row175_pos at_branch .old

theorem envelope_row176 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row176_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row177 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row177_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row178 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row178_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row179 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row179_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row180 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row180_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row181 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row181_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row182 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row182_pos at_branch .old

theorem envelope_row183 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row183_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row184 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row184_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row185 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row185_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row186 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row186_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row187 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row187_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row188 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row188_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row189 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row189_pos at_branch .old

theorem envelope_row190 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row190_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row191 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row191_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row192 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row192_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row193 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row193_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row194 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row194_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row195 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row195_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row196 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row196_pos at_branch .old

theorem envelope_row197 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row197_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row198 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row198_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row199 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row199_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row200 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row200_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row201 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row201_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row202 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row202_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row203 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row203_pos at_branch .old

theorem envelope_row204 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row204_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row205 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row205_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row206 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row206_pos at_branch .Pcountmid at_window returnWindow277 with_member window277_mem box((53/128:ℝ),(425/1024:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row207 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row207_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row208 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row208_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row209 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row209_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row210 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row210_pos at_branch .old

theorem envelope_row211 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row211_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row212 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row212_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row213 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row213_pos at_branch .Pcountmid at_window returnWindow278 with_member window278_mem box((425/1024:ℝ),(213/512:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row214 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row214_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row215 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row215_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row216 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row216_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row217 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row217_pos at_branch .old

theorem envelope_row218 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row218_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row219 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row219_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row220 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row220_pos at_branch .Pcountmid at_window returnWindow279 with_member window279_mem box((213/512:ℝ),(427/1024:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row221 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row221_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row222 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row222_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row223 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row223_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row224 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row224_pos at_branch .old

theorem envelope_row225 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row225_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row226 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row226_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row227 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row227_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row228 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row228_pos at_branch .Pcountmid at_window returnWindow280 with_member window280_mem box((427/1024:ℝ),(107/256:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row229 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row229_pos at_branch .Pcount at_window returnWindow262 with_member window262_mem box((427/1024:ℝ),(107/256:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row230 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row230_pos at_branch .Pcount at_window returnWindow262 with_member window262_mem box((427/1024:ℝ),(107/256:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row231 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row231_pos at_branch .old

theorem envelope_row232 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row232_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row233 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row233_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row234 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row234_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row235 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row235_pos at_branch .Pcountmid at_window returnWindow281 with_member window281_mem box((107/256:ℝ),(429/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row236 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row236_pos at_branch .Pcountmid at_window returnWindow281 with_member window281_mem box((107/256:ℝ),(429/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row237 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row237_pos at_branch .Pcount at_window returnWindow263 with_member window263_mem box((107/256:ℝ),(429/1024:ℝ),(127/256:ℝ),(1/2:ℝ))

theorem envelope_row238 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row238_pos at_branch .old

theorem envelope_row239 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row239_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row240 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row240_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row241 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row241_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row242 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row242_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row243 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row243_pos at_branch .Pcountmid at_window returnWindow282 with_member window282_mem box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row244 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row244_pos at_branch .Pcountmid at_window returnWindow282 with_member window282_mem box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row245 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row245_pos at_branch .old

theorem envelope_row246 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row246_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row247 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row247_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row248 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row248_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row249 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row249_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row250 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row250_pos at_branch .Pcountmid at_window returnWindow283 with_member window283_mem box((215/512:ℝ),(431/1024:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row251 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row251_pos at_branch .Pcountmid at_window returnWindow283 with_member window283_mem box((215/512:ℝ),(431/1024:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row252 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row252_pos at_branch .old

theorem envelope_row253 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row253_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row254 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row254_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row255 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row255_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row256 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row256_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row257 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row257_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row258 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row258_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row259 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row259_pos at_branch .old

theorem envelope_row260 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row260_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row261 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row261_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row262 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row262_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row263 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row263_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row264 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row264_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row265 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row265_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row266 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row266_pos at_branch .old

theorem envelope_row267 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row267_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row268 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row268_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row269 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row269_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row270 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row270_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row271 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row271_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row272 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row272_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row273 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row273_pos at_branch .old

theorem envelope_row274 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row274_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row275 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row275_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row276 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row276_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row277 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row277_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row278 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row278_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row279 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row279_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row280 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row280_pos at_branch .old

theorem envelope_row281 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row281_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row282 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row282_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row283 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row283_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row284 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row284_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row285 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row285_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row286 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row286_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row287 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row287_pos at_branch .old

theorem envelope_row288 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row288_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row289 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row289_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row290 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row290_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row291 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row291_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row292 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row292_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row293 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row293_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row294 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row294_pos at_branch .old

theorem envelope_row295 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row295_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row296 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row296_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row297 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row297_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row298 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row298_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row299 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row299_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row300 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row300_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row301 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row301_pos at_branch .old

theorem envelope_row302 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row302_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row303 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row303_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row304 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row304_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row305 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row305_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row306 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row306_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row307 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row307_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row308 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row308_pos at_branch .old

theorem envelope_row309 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row309_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row310 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row310_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row311 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row311_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row312 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row312_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row313 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row313_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row314 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row314_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row315 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row315_pos at_branch .old

theorem envelope_row316 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row316_pos at_branch .old

theorem envelope_row317 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row317_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row318 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row318_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row319 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row319_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row320 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row320_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row321 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row321_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row322 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row322_pos at_branch .old

theorem envelope_row323 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row323_pos at_branch .old

theorem envelope_row324 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row324_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row325 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row325_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row326 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row326_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row327 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row327_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row328 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row328_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row329 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row329_pos at_branch .old

theorem envelope_row330 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row330_pos at_branch .old

theorem envelope_row331 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row331_pos at_branch .old

theorem envelope_row332 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row332_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row333 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row333_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row334 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row334_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row335 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row335_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row336 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row336_pos at_branch .old

theorem envelope_row337 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row337_pos at_branch .old

theorem envelope_row338 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row338_pos at_branch .old

theorem envelope_row339 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row339_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row340 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row340_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row341 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row341_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row342 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row342_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row343 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row343_pos at_branch .old

theorem envelope_row344 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row344_pos at_branch .old

theorem envelope_row345 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row345_pos at_branch .old

theorem envelope_row346 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row346_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row347 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row347_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row348 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row348_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row349 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row349_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row350 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row350_pos at_branch .old

theorem envelope_row351 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row351_pos at_branch .old

theorem envelope_row352 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row352_pos at_branch .old

theorem envelope_row353 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row353_pos at_branch .old

theorem envelope_row354 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row354_pos at_branch .old

theorem envelope_row355 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row355_pos at_branch .old

theorem envelope_row356 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row356_pos at_branch .old

theorem envelope_row357 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row357_pos at_branch .old

theorem envelope_row358 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row358_pos at_branch .old

theorem envelope_row359 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row359_pos at_branch .old

theorem envelope_row360 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row360_pos at_branch .old

theorem envelope_row361 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row361_pos at_branch .old

theorem envelope_row362 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row362_pos at_branch .old

theorem envelope_row363 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row363_pos at_branch .old

theorem envelope_row364 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row364_pos at_branch .old

theorem envelope_row365 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row365_pos at_branch .old

theorem envelope_row366 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row366_pos at_branch .old

theorem envelope_row367 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row367_pos at_branch .old

theorem envelope_row368 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row368_pos at_branch .old

theorem envelope_row369 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row369_pos at_branch .old

theorem envelope_row370 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row370_pos at_branch .old

theorem envelope_row371 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row371_pos at_branch .old

theorem envelope_row372 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row372_pos at_branch .old

theorem envelope_row373 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row373_pos at_branch .old

theorem envelope_row374 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row374_pos at_branch .old

theorem envelope_row375 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row375_pos at_branch .old

theorem envelope_row376 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row376_pos at_branch .old

theorem envelope_row377 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row377_pos at_branch .old

theorem envelope_row378 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row378_pos at_branch .old

theorem envelope_row379 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row379_pos at_branch .old

theorem envelope_row380 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row380_pos at_branch .old

theorem envelope_row381 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row381_pos at_branch .old

theorem envelope_row382 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row382_pos at_branch .old

theorem envelope_row383 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row383_pos at_branch .old

theorem envelope_row384 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row384_pos at_branch .old

theorem envelope_row385 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row385_pos at_branch .old

theorem envelope_row386 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row386_pos at_branch .old

theorem envelope_row387 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row387_pos at_branch .old

theorem envelope_row388 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row388_pos at_branch .old

theorem envelope_row389 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row389_pos at_branch .old

theorem envelope_row390 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row390_pos at_branch .old

theorem envelope_row391 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row391_pos at_branch .old

theorem envelope_row392 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row392_pos at_branch .old

theorem envelope_row393 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row393_pos at_branch .old

theorem envelope_row394 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row394_pos at_branch .old

theorem envelope_row395 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row395_pos at_branch .old

theorem envelope_row396 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row396_pos at_branch .old

theorem envelope_row397 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row397_pos at_branch .old

theorem envelope_row398 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row398_pos at_branch .old

theorem envelope_row399 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row399_pos at_branch .old

theorem envelope_row400 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row400_pos at_branch .old

theorem envelope_row401 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row401_pos at_branch .old

theorem envelope_row402 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row402_pos at_branch .old

theorem envelope_row403 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row403_pos at_branch .old

theorem envelope_row404 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row404_pos at_branch .old

theorem envelope_row405 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row405_pos at_branch .old

theorem envelope_row406 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row406_pos at_branch .old

theorem envelope_row407 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row407_pos at_branch .old

theorem envelope_row408 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row408_pos at_branch .old

theorem envelope_row409 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row409_pos at_branch .old

theorem envelope_row410 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row410_pos at_branch .old

theorem envelope_row411 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row411_pos at_branch .old

theorem envelope_row412 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row412_pos at_branch .old

theorem envelope_row413 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row413_pos at_branch .old

theorem envelope_row414 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row414_pos at_branch .old

theorem envelope_row415 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row415_pos at_branch .old

theorem envelope_row416 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row416_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row417 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row417_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row418 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row418_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row419 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row419_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row420 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row420_pos at_branch .old

theorem envelope_row421 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row421_pos at_branch .old

theorem envelope_row422 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row422_pos at_branch .old

theorem envelope_row423 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row423_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row424 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row424_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row425 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row425_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row426 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row426_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row427 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row427_pos at_branch .old

theorem envelope_row428 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row428_pos at_branch .old

theorem envelope_row429 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row429_pos at_branch .old

theorem envelope_row430 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row430_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row431 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row431_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row432 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row432_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row433 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_window hδ, hp using row433_pos at_branch .Pnew at_window returnWindow10 with_member window10_mem box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row434 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row434_pos at_branch .old

theorem envelope_row435 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row435_pos at_branch .old

theorem envelope_row436 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row436_pos at_branch .old

theorem envelope_row437 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row437_pos at_branch .old

theorem envelope_row438 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row438_pos at_branch .old

theorem envelope_row439 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row439_pos at_branch .old

theorem envelope_row440 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row440_pos at_branch .old

theorem envelope_row441 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row441_pos at_branch .old

theorem envelope_row442 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row442_pos at_branch .old

theorem envelope_row443 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row443_pos at_branch .old

theorem envelope_row444 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row444_pos at_branch .old

theorem envelope_row445 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row445_pos at_branch .old

theorem envelope_row446 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row446_pos at_branch .old

theorem envelope_row447 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSmall δ p := by
  return_old hδ, hp using row447_pos at_branch .old

theorem envelope_row448 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row448_pos at_branch .old

theorem envelope_row449 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row449_pos at_branch .old

theorem envelope_row450 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row450_pos at_branch .old

theorem envelope_row451 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row451_pos at_branch .old

theorem envelope_row452 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row452_pos at_branch .old

theorem envelope_row453 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row453_pos at_branch .old

theorem envelope_row454 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row454_pos at_branch .old

theorem envelope_row455 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row455_pos at_branch .old

theorem envelope_row456 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row456_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row457 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row457_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row458 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row458_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row459 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row459_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row460 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row460_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row461 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row461_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row462 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row462_pos at_branch .old

theorem envelope_row463 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row463_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row464 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row464_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row465 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row465_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row466 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row466_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row467 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row467_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row468 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row468_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row469 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row469_pos at_branch .old

theorem envelope_row470 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row470_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row471 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row471_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row472 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row472_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row473 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row473_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row474 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row474_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row475 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row475_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row476 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row476_pos at_branch .old

theorem envelope_row477 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row477_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row478 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row478_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row479 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row479_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row480 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row480_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row481 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row481_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row482 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row482_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row483 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row483_pos at_branch .old

theorem envelope_row484 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row484_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row485 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row485_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row486 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row486_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row487 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row487_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row488 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row488_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row489 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row489_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row490 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row490_pos at_branch .old

theorem envelope_row491 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row491_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row492 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row492_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row493 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row493_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row494 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row494_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row495 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row495_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row496 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row496_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row497 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row497_pos at_branch .old

theorem envelope_row498 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row498_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row499 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row499_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row500 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row500_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row501 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row501_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row502 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row502_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row503 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row503_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row504 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row504_pos at_branch .old

theorem envelope_row505 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row505_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row506 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row506_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row507 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row507_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row508 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row508_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row509 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row509_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row510 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row510_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row511 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row511_pos at_branch .old

theorem envelope_row512 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row512_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row513 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row513_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row514 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row514_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row515 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row515_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row516 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row516_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row517 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row517_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row518 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row518_pos at_branch .old

theorem envelope_row519 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row519_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row520 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row520_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row521 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row521_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row522 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row522_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row523 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row523_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row524 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row524_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row525 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row525_pos at_branch .old

theorem envelope_row526 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row526_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row527 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row527_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row528 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row528_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row529 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row529_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row530 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row530_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row531 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row531_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row532 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row532_pos at_branch .old

theorem envelope_row533 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row533_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row534 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row534_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row535 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row535_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row536 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row536_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row537 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row537_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row538 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row538_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row539 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row539_pos at_branch .old

theorem envelope_row540 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row540_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row541 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row541_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row542 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row542_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row543 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row543_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row544 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row544_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row545 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row545_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row546 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row546_pos at_branch .old

theorem envelope_row547 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row547_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row548 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row548_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row549 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row549_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row550 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row550_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row551 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row551_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row552 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row552_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row553 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row553_pos at_branch .old

theorem envelope_row554 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row554_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row555 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row555_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row556 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row556_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row557 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row557_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row558 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row558_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row559 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row559_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row560 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row560_pos at_branch .old

theorem envelope_row561 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row561_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row562 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row562_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row563 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row563_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row564 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row564_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row565 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row565_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row566 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row566_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row567 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row567_pos at_branch .old

theorem envelope_row568 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row568_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row569 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row569_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row570 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row570_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row571 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row571_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row572 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row572_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row573 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row573_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row574 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row574_pos at_branch .old

theorem envelope_row575 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row575_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row576 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row576_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row577 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row577_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row578 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row578_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row579 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row579_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row580 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row580_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row581 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row581_pos at_branch .old

theorem envelope_row582 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row582_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row583 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row583_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row584 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row584_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row585 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row585_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row586 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row586_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row587 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row587_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row588 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row588_pos at_branch .old

theorem envelope_row589 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row589_pos at_branch .Pwide at_window returnWindow90 with_member window90_mem box((51/128:ℝ),(13/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row590 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row590_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row591 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row591_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row592 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row592_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row593 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row593_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row594 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row594_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row595 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row595_pos at_branch .old

theorem envelope_row596 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row596_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row597 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row597_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row598 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row598_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row599 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row599_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row600 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row600_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row601 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row601_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row602 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row602_pos at_branch .old

theorem envelope_row603 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row603_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row604 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row604_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row605 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row605_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row606 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row606_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row607 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row607_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row608 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row608_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row609 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row609_pos at_branch .old

theorem envelope_row610 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row610_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row611 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row611_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row612 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row612_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row613 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row613_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row614 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row614_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row615 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row615_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row616 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row616_pos at_branch .old

theorem envelope_row617 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row617_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row618 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row618_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row619 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row619_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row620 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row620_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row621 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row621_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row622 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row622_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row623 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row623_pos at_branch .old

theorem envelope_row624 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row624_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row625 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row625_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row626 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row626_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row627 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row627_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row628 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row628_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row629 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row629_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row630 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row630_pos at_branch .old

theorem envelope_row631 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row631_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row632 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row632_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row633 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row633_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row634 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row634_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row635 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row635_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row636 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row636_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row637 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row637_pos at_branch .old

theorem envelope_row638 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row638_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row639 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row639_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row640 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row640_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row641 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row641_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row642 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row642_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row643 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row643_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row644 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row644_pos at_branch .old

theorem envelope_row645 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row645_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row646 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row646_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row647 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row647_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row648 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row648_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row649 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row649_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row650 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row650_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row651 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row651_pos at_branch .old

theorem envelope_row652 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row652_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row653 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row653_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row654 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row654_pos at_branch .Pcountmid at_window returnWindow277 with_member window277_mem box((53/128:ℝ),(425/1024:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row655 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row655_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row656 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row656_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row657 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row657_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row658 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row658_pos at_branch .old

theorem envelope_row659 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row659_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row660 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row660_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row661 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row661_pos at_branch .Pcountmid at_window returnWindow278 with_member window278_mem box((425/1024:ℝ),(213/512:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row662 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row662_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row663 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row663_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row664 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row664_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row665 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row665_pos at_branch .old

theorem envelope_row666 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row666_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row667 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row667_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row668 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row668_pos at_branch .Pcountmid at_window returnWindow279 with_member window279_mem box((213/512:ℝ),(427/1024:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row669 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row669_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row670 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row670_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row671 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row671_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row672 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row672_pos at_branch .old

theorem envelope_row673 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row673_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row674 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row674_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row675 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row675_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row676 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row676_pos at_branch .Pcountmid at_window returnWindow280 with_member window280_mem box((427/1024:ℝ),(107/256:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row677 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row677_pos at_branch .Pcount at_window returnWindow262 with_member window262_mem box((427/1024:ℝ),(107/256:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row678 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row678_pos at_branch .Pcount at_window returnWindow262 with_member window262_mem box((427/1024:ℝ),(107/256:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row679 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row679_pos at_branch .old

theorem envelope_row680 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row680_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row681 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row681_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row682 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row682_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row683 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row683_pos at_branch .Pcountmid at_window returnWindow281 with_member window281_mem box((107/256:ℝ),(429/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row684 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row684_pos at_branch .Pcountmid at_window returnWindow281 with_member window281_mem box((107/256:ℝ),(429/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row685 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row685_pos at_branch .Pcount at_window returnWindow263 with_member window263_mem box((107/256:ℝ),(429/1024:ℝ),(127/256:ℝ),(1/2:ℝ))

theorem envelope_row686 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row686_pos at_branch .old

theorem envelope_row687 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row687_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row688 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row688_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row689 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row689_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row690 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row690_pos at_branch .Cbridge3 at_window returnWindow168 with_member window168_mem box((429/1024:ℝ),(215/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row691 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row691_pos at_branch .Pcountmid at_window returnWindow282 with_member window282_mem box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row692 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row692_pos at_branch .Pcountmid at_window returnWindow282 with_member window282_mem box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row693 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row693_pos at_branch .old

theorem envelope_row694 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row694_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row695 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row695_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row696 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row696_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row697 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row697_pos at_branch .Cbridge5 at_window returnWindow209 with_member window209_mem box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row698 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row698_pos at_branch .Pcountmid at_window returnWindow283 with_member window283_mem box((215/512:ℝ),(431/1024:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row699 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row699_pos at_branch .Pcountmid at_window returnWindow283 with_member window283_mem box((215/512:ℝ),(431/1024:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row700 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row700_pos at_branch .old

theorem envelope_row701 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row701_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row702 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row702_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row703 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row703_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row704 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row704_pos at_branch .Cbridge5 at_window returnWindow210 with_member window210_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row705 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row705_pos at_branch .Cnew at_window returnWindow52 with_member window52_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row706 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row706_pos at_branch .Cnew at_window returnWindow52 with_member window52_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row707 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row707_pos at_branch .old

theorem envelope_row708 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row708_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row709 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row709_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row710 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row710_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row711 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row711_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row712 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row712_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row713 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row713_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row714 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row714_pos at_branch .old

theorem envelope_row715 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row715_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row716 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row716_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row717 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row717_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row718 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row718_pos at_branch .Cbridge4 at_window returnWindow187 with_member window187_mem box((433/1024:ℝ),(217/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row719 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row719_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row720 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row720_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row721 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row721_pos at_branch .old

theorem envelope_row722 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row722_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row723 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row723_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row724 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row724_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row725 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row725_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row726 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row726_pos at_branch .Cbridge4 at_window returnWindow188 with_member window188_mem box((217/512:ℝ),(435/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row727 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row727_pos at_branch .Cbridge4 at_window returnWindow188 with_member window188_mem box((217/512:ℝ),(435/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row728 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row728_pos at_branch .old

theorem envelope_row729 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row729_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row730 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row730_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row731 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row731_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row732 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row732_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row733 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row733_pos at_branch .Cbridge6 at_window returnWindow227 with_member window227_mem box((435/1024:ℝ),(109/256:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row734 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row734_pos at_branch .Cbridge6 at_window returnWindow227 with_member window227_mem box((435/1024:ℝ),(109/256:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row735 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row735_pos at_branch .old

theorem envelope_row736 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row736_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row737 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row737_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row738 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row738_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row739 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row739_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row740 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row740_pos at_branch .Cbridge6 at_window returnWindow228 with_member window228_mem box((109/256:ℝ),(437/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row741 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row741_pos at_branch .Cbridge6 at_window returnWindow228 with_member window228_mem box((109/256:ℝ),(437/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row742 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row742_pos at_branch .old

theorem envelope_row743 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row743_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row744 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row744_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row745 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row745_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row746 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row746_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row747 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row747_pos at_branch .Cbridge6 at_window returnWindow229 with_member window229_mem box((437/1024:ℝ),(219/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row748 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row748_pos at_branch .Cbridge6 at_window returnWindow229 with_member window229_mem box((437/1024:ℝ),(219/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row749 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row749_pos at_branch .old

theorem envelope_row750 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row750_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row751 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row751_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row752 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row752_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row753 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row753_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row754 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row754_pos at_branch .Cbridge6 at_window returnWindow230 with_member window230_mem box((219/512:ℝ),(439/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row755 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row755_pos at_branch .Cbridge6 at_window returnWindow230 with_member window230_mem box((219/512:ℝ),(439/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row756 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row756_pos at_branch .old

theorem envelope_row757 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row757_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row758 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row758_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row759 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row759_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row760 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row760_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row761 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row761_pos at_branch .Cbridge6 at_window returnWindow231 with_member window231_mem box((439/1024:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row762 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row762_pos at_branch .Cbridge6 at_window returnWindow231 with_member window231_mem box((439/1024:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row763 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row763_pos at_branch .old

theorem envelope_row764 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row764_pos at_branch .Cbridge0 at_window returnWindow103 with_member window103_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row765 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row765_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row766 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row766_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row767 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row767_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row768 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row768_pos at_branch .Cbridge4 at_window returnWindow194 with_member window194_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row769 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row769_pos at_branch .Cbridge4 at_window returnWindow194 with_member window194_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row770 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row770_pos at_branch .old

theorem envelope_row771 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row771_pos at_branch .Cbridge0 at_window returnWindow103 with_member window103_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row772 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row772_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row773 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row773_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row774 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row774_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row775 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row775_pos at_branch .Cbridge4 at_window returnWindow194 with_member window194_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row776 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row776_pos at_branch .Cbridge4 at_window returnWindow194 with_member window194_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row777 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row777_pos at_branch .old

theorem envelope_row778 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row778_pos at_branch .Cbridge0 at_window returnWindow104 with_member window104_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row779 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row779_pos at_branch .Cbridge1 at_window returnWindow130 with_member window130_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row780 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row780_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row781 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row781_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row782 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row782_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row783 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row783_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row784 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row784_pos at_branch .old

theorem envelope_row785 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row785_pos at_branch .Cbridge0 at_window returnWindow104 with_member window104_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row786 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row786_pos at_branch .Cbridge1 at_window returnWindow130 with_member window130_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row787 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row787_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row788 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row788_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row789 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row789_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row790 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row790_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row791 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row791_pos at_branch .old

theorem envelope_row792 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row792_pos at_branch .Cbridge0 at_window returnWindow104 with_member window104_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row793 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row793_pos at_branch .Cbridge1 at_window returnWindow130 with_member window130_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row794 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row794_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row795 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row795_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row796 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row796_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row797 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row797_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row798 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row798_pos at_branch .old

theorem envelope_row799 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row799_pos at_branch .Cbridge0 at_window returnWindow105 with_member window105_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row800 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row800_pos at_branch .Cphys at_window returnWindow11 with_member window11_mem box((3/8:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row801 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row801_pos at_branch .Cbridge2 at_window returnWindow154 with_member window154_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row802 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row802_pos at_branch .Cbridge3 at_window returnWindow174 with_member window174_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row803 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row803_pos at_branch .Cbridge5 at_window returnWindow214 with_member window214_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row804 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row804_pos at_branch .Cbridge5 at_window returnWindow214 with_member window214_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row805 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row805_pos at_branch .old

theorem envelope_row806 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row806_pos at_branch .Cbridge0 at_window returnWindow106 with_member window106_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row807 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row807_pos at_branch .Cphys at_window returnWindow11 with_member window11_mem box((3/8:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row808 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row808_pos at_branch .Cbridge2 at_window returnWindow155 with_member window155_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row809 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row809_pos at_branch .Cbridge3 at_window returnWindow175 with_member window175_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row810 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row810_pos at_branch .Cbridge3 at_window returnWindow175 with_member window175_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row811 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row811_pos at_branch .Cbridge5 at_window returnWindow215 with_member window215_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row812 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row812_pos at_branch .old

theorem envelope_row813 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row813_pos at_branch .Cbridge0 at_window returnWindow107 with_member window107_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row814 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row814_pos at_branch .Cphys at_window returnWindow11 with_member window11_mem box((3/8:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row815 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row815_pos at_branch .Cbridge2 at_window returnWindow156 with_member window156_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row816 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row816_pos at_branch .Cbridge3 at_window returnWindow176 with_member window176_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row817 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row817_pos at_branch .Cbridge3 at_window returnWindow176 with_member window176_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row818 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row818_pos at_branch .Cbridge3 at_window returnWindow176 with_member window176_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row819 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row819_pos at_branch .old

theorem envelope_row820 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row820_pos at_branch .Cbridge0 at_window returnWindow108 with_member window108_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row821 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row821_pos at_branch .Cphys at_window returnWindow22 with_member window22_mem box((15/32:ℝ),(33/64:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row822 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row822_pos at_branch .Cbridge2 at_window returnWindow157 with_member window157_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row823 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row823_pos at_branch .Cbridge2 at_window returnWindow157 with_member window157_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row824 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row824_pos at_branch .Cbridge3 at_window returnWindow177 with_member window177_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row825 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row825_pos at_branch .Cbridge3 at_window returnWindow177 with_member window177_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row826 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row826_pos at_branch .old

theorem envelope_row827 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row827_pos at_branch .Cbridge0 at_window returnWindow109 with_member window109_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row828 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row828_pos at_branch .Cphys at_window returnWindow22 with_member window22_mem box((15/32:ℝ),(33/64:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row829 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row829_pos at_branch .Cbridge1 at_window returnWindow135 with_member window135_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row830 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row830_pos at_branch .Cbridge2 at_window returnWindow158 with_member window158_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row831 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row831_pos at_branch .Cbridge3 at_window returnWindow178 with_member window178_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row832 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row832_pos at_branch .Cbridge3 at_window returnWindow178 with_member window178_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row833 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row833_pos at_branch .old

theorem envelope_row834 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row834_pos at_branch .Cbridge0 at_window returnWindow110 with_member window110_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row835 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row835_pos at_branch .Cbridge0 at_window returnWindow110 with_member window110_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row836 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row836_pos at_branch .Cbridge1 at_window returnWindow136 with_member window136_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row837 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row837_pos at_branch .Cbridge2 at_window returnWindow159 with_member window159_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row838 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row838_pos at_branch .Cbridge2 at_window returnWindow159 with_member window159_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row839 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row839_pos at_branch .Cbridge2 at_window returnWindow159 with_member window159_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row840 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row840_pos at_branch .old

theorem envelope_row841 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row841_pos at_branch .Cbridge0 at_window returnWindow111 with_member window111_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row842 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row842_pos at_branch .Cbridge0 at_window returnWindow111 with_member window111_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row843 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row843_pos at_branch .Cbridge1 at_window returnWindow137 with_member window137_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row844 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row844_pos at_branch .Cbridge2 at_window returnWindow160 with_member window160_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row845 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row845_pos at_branch .Cbridge2 at_window returnWindow160 with_member window160_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row846 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row846_pos at_branch .Cbridge2 at_window returnWindow160 with_member window160_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row847 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row847_pos at_branch .old

theorem envelope_row848 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row848_pos at_branch .Cbridge0 at_window returnWindow112 with_member window112_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row849 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row849_pos at_branch .Cbridge0 at_window returnWindow112 with_member window112_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row850 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row850_pos at_branch .Cbridge1 at_window returnWindow138 with_member window138_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row851 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row851_pos at_branch .Cbridge2 at_window returnWindow161 with_member window161_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row852 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row852_pos at_branch .Cbridge2 at_window returnWindow161 with_member window161_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row853 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row853_pos at_branch .Cbridge2 at_window returnWindow161 with_member window161_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row854 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row854_pos at_branch .old

theorem envelope_row855 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row855_pos at_branch .Cbridge0 at_window returnWindow113 with_member window113_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row856 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row856_pos at_branch .Cbridge0 at_window returnWindow113 with_member window113_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row857 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row857_pos at_branch .Cbridge1 at_window returnWindow139 with_member window139_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row858 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row858_pos at_branch .Cbridge1 at_window returnWindow139 with_member window139_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row859 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row859_pos at_branch .Cbridge2 at_window returnWindow162 with_member window162_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row860 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row860_pos at_branch .Cbridge2 at_window returnWindow162 with_member window162_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row861 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row861_pos at_branch .old

theorem envelope_row862 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row862_pos at_branch .Cbridge0 at_window returnWindow114 with_member window114_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row863 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row863_pos at_branch .Cbridge0 at_window returnWindow114 with_member window114_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row864 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row864_pos at_branch .Cbridge1 at_window returnWindow140 with_member window140_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row865 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row865_pos at_branch .Cbridge1 at_window returnWindow140 with_member window140_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row866 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row866_pos at_branch .Cbridge2 at_window returnWindow163 with_member window163_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row867 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row867_pos at_branch .Cbridge2 at_window returnWindow163 with_member window163_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row868 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row868_pos at_branch .old

theorem envelope_row869 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row869_pos at_branch .Cbridge0 at_window returnWindow115 with_member window115_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row870 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row870_pos at_branch .Cbridge0 at_window returnWindow115 with_member window115_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row871 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row871_pos at_branch .Cphys at_window returnWindow76 with_member window76_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row872 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row872_pos at_branch .Cbridge1 at_window returnWindow141 with_member window141_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row873 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row873_pos at_branch .Cbridge1 at_window returnWindow141 with_member window141_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row874 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row874_pos at_branch .Cbridge1 at_window returnWindow141 with_member window141_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row875 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row875_pos at_branch .old

theorem envelope_row876 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row876_pos at_branch .Cbridge0 at_window returnWindow116 with_member window116_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row877 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row877_pos at_branch .Cbridge0 at_window returnWindow116 with_member window116_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row878 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row878_pos at_branch .Cphys at_window returnWindow77 with_member window77_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row879 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row879_pos at_branch .Cbridge1 at_window returnWindow142 with_member window142_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row880 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row880_pos at_branch .Cbridge1 at_window returnWindow142 with_member window142_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row881 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row881_pos at_branch .Cbridge1 at_window returnWindow142 with_member window142_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row882 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row882_pos at_branch .old

theorem envelope_row883 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row883_pos at_branch .Cbridge0 at_window returnWindow117 with_member window117_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row884 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row884_pos at_branch .Cbridge0 at_window returnWindow117 with_member window117_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row885 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row885_pos at_branch .Cbridge0 at_window returnWindow117 with_member window117_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row886 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row886_pos at_branch .Cphys at_window returnWindow78 with_member window78_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row887 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row887_pos at_branch .Cphys at_window returnWindow78 with_member window78_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row888 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_window hδ, hp using row888_pos at_branch .Cphys at_window returnWindow78 with_member window78_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row889 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row889_pos at_branch .old

theorem envelope_row890 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row890_pos at_branch .old

theorem envelope_row891 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row891_pos at_branch .old

theorem envelope_row892 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row892_pos at_branch .old

theorem envelope_row893 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row893_pos at_branch .old

theorem envelope_row894 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row894_pos at_branch .old

theorem envelope_row895 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .oldSwitch δ p := by
  return_old hδ, hp using row895_pos at_branch .old

theorem envelope_row896 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row896_pos at_branch .old

theorem envelope_row897 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row897_pos at_branch .old

theorem envelope_row898 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row898_pos at_branch .old

theorem envelope_row899 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row899_pos at_branch .old

theorem envelope_row900 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row900_pos at_branch .old

theorem envelope_row901 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row901_pos at_branch .old

theorem envelope_row902 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row902_pos at_branch .old

theorem envelope_row903 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row903_pos at_branch .old

theorem envelope_row904 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row904_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row905 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row905_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row906 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row906_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row907 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row907_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row908 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row908_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row909 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row909_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row910 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row910_pos at_branch .old

theorem envelope_row911 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row911_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row912 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row912_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row913 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row913_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row914 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row914_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row915 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row915_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row916 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row916_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row917 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row917_pos at_branch .old

theorem envelope_row918 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row918_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row919 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row919_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row920 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row920_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row921 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row921_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row922 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row922_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row923 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row923_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row924 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row924_pos at_branch .old

theorem envelope_row925 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row925_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row926 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row926_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row927 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row927_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row928 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row928_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row929 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row929_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row930 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row930_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row931 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row931_pos at_branch .old

theorem envelope_row932 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row932_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row933 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row933_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row934 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row934_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row935 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row935_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row936 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row936_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row937 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row937_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row938 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row938_pos at_branch .old

theorem envelope_row939 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row939_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row940 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row940_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row941 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row941_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row942 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row942_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row943 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row943_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row944 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row944_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row945 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row945_pos at_branch .old

theorem envelope_row946 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row946_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row947 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row947_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row948 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row948_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row949 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row949_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row950 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row950_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row951 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row951_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row952 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row952_pos at_branch .old

theorem envelope_row953 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row953_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row954 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row954_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row955 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row955_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row956 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row956_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row957 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row957_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row958 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row958_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row959 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row959_pos at_branch .old

theorem envelope_row960 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row960_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row961 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row961_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row962 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row962_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row963 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row963_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row964 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row964_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row965 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row965_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row966 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row966_pos at_branch .old

theorem envelope_row967 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row967_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row968 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row968_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row969 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row969_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row970 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row970_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row971 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row971_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row972 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row972_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row973 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row973_pos at_branch .old

theorem envelope_row974 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row974_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row975 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row975_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row976 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row976_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row977 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row977_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row978 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row978_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row979 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row979_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row980 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row980_pos at_branch .old

theorem envelope_row981 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row981_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row982 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row982_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row983 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row983_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row984 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row984_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row985 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row985_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row986 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row986_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row987 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row987_pos at_branch .old

theorem envelope_row988 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row988_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row989 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row989_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row990 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row990_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row991 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row991_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row992 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row992_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row993 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row993_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row994 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row994_pos at_branch .old

theorem envelope_row995 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row995_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row996 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row996_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row997 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row997_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row998 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row998_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row999 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row999_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1000 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1000_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1001 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1001_pos at_branch .old

theorem envelope_row1002 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1002_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1003 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1003_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1004 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1004_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1005 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1005_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1006 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1006_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1007 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1007_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1008 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1008_pos at_branch .old

theorem envelope_row1009 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1009_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1010 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1010_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1011 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1011_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1012 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1012_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1013 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1013_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1014 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1014_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1015 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1015_pos at_branch .old

theorem envelope_row1016 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1016_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1017 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1017_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1018 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1018_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1019 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1019_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1020 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1020_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1021 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1021_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1022 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1022_pos at_branch .old

theorem envelope_row1023 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1023_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1024 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1024_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1025 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1025_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1026 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1026_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1027 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1027_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1028 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1028_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1029 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1029_pos at_branch .old

theorem envelope_row1030 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1030_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1031 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1031_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1032 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1032_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1033 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1033_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1034 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1034_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1035 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1035_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1036 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1036_pos at_branch .old

theorem envelope_row1037 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1037_pos at_branch .Pwide at_window returnWindow90 with_member window90_mem box((51/128:ℝ),(13/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1038 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1038_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1039 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1039_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1040 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1040_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1041 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1041_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1042 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1042_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1043 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1043_pos at_branch .old

theorem envelope_row1044 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1044_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1045 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1045_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1046 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1046_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1047 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1047_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1048 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1048_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1049 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1049_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1050 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1050_pos at_branch .old

theorem envelope_row1051 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1051_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1052 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1052_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1053 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1053_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1054 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1054_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1055 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1055_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1056 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1056_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1057 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1057_pos at_branch .old

theorem envelope_row1058 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1058_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1059 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1059_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1060 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1060_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1061 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1061_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1062 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1062_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1063 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1063_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1064 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1064_pos at_branch .old

theorem envelope_row1065 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1065_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1066 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1066_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1067 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1067_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1068 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1068_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1069 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1069_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1070 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1070_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1071 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1071_pos at_branch .old

theorem envelope_row1072 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1072_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1073 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1073_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1074 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1074_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1075 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1075_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1076 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1076_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1077 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1077_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1078 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1078_pos at_branch .old

theorem envelope_row1079 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1079_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1080 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1080_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1081 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1081_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1082 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1082_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1083 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1083_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1084 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1084_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1085 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1085_pos at_branch .old

theorem envelope_row1086 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1086_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1087 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1087_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1088 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1088_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1089 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1089_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1090 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1090_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1091 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1091_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1092 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1092_pos at_branch .old

theorem envelope_row1093 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1093_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1094 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1094_pos at_branch .Pwide at_window returnWindow91 with_member window91_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1095 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1095_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1096 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1096_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1097 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1097_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1098 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1098_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1099 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1099_pos at_branch .old

theorem envelope_row1100 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1100_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1101 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1101_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1102 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1102_pos at_branch .Pcountmid at_window returnWindow277 with_member window277_mem box((53/128:ℝ),(425/1024:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1103 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1103_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1104 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1104_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1105 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1105_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1106 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1106_pos at_branch .old

theorem envelope_row1107 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1107_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1108 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1108_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1109 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1109_pos at_branch .Pcountmid at_window returnWindow278 with_member window278_mem box((425/1024:ℝ),(213/512:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1110 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1110_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1111 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1111_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1112 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1112_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1113 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1113_pos at_branch .old

theorem envelope_row1114 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1114_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1115 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1115_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1116 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1116_pos at_branch .Pcountmid at_window returnWindow279 with_member window279_mem box((213/512:ℝ),(427/1024:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1117 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1117_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1118 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1118_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1119 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1119_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1120 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1120_pos at_branch .old

theorem envelope_row1121 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1121_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1122 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1122_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1123 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1123_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1124 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1124_pos at_branch .Pcountmid at_window returnWindow280 with_member window280_mem box((427/1024:ℝ),(107/256:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1125 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1125_pos at_branch .Pcount at_window returnWindow262 with_member window262_mem box((427/1024:ℝ),(107/256:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row1126 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1126_pos at_branch .Pcount at_window returnWindow262 with_member window262_mem box((427/1024:ℝ),(107/256:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row1127 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1127_pos at_branch .old

theorem envelope_row1128 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1128_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1129 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1129_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1130 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1130_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1131 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1131_pos at_branch .Pcountmid at_window returnWindow281 with_member window281_mem box((107/256:ℝ),(429/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1132 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1132_pos at_branch .Pcountmid at_window returnWindow281 with_member window281_mem box((107/256:ℝ),(429/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1133 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1133_pos at_branch .Pcount at_window returnWindow263 with_member window263_mem box((107/256:ℝ),(429/1024:ℝ),(127/256:ℝ),(1/2:ℝ))

theorem envelope_row1134 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1134_pos at_branch .old

theorem envelope_row1135 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1135_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1136 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1136_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1137 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1137_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1138 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1138_pos at_branch .Cbridge3 at_window returnWindow168 with_member window168_mem box((429/1024:ℝ),(215/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1139 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1139_pos at_branch .Pcountmid at_window returnWindow282 with_member window282_mem box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row1140 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1140_pos at_branch .Pcountmid at_window returnWindow282 with_member window282_mem box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row1141 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1141_pos at_branch .old

theorem envelope_row1142 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1142_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1143 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1143_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1144 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1144_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1145 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1145_pos at_branch .Cbridge5 at_window returnWindow209 with_member window209_mem box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1146 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1146_pos at_branch .Pcountmid at_window returnWindow283 with_member window283_mem box((215/512:ℝ),(431/1024:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row1147 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1147_pos at_branch .Pcountmid at_window returnWindow283 with_member window283_mem box((215/512:ℝ),(431/1024:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row1148 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1148_pos at_branch .old

theorem envelope_row1149 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1149_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1150 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1150_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1151 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1151_pos at_branch .Pwide at_window returnWindow92 with_member window92_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1152 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1152_pos at_branch .Cbridge5 at_window returnWindow210 with_member window210_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1153 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1153_pos at_branch .Cnew at_window returnWindow52 with_member window52_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1154 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1154_pos at_branch .Cnew at_window returnWindow52 with_member window52_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1155 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1155_pos at_branch .old

theorem envelope_row1156 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1156_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1157 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1157_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1158 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1158_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1159 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1159_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1160 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1160_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1161 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1161_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1162 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1162_pos at_branch .old

theorem envelope_row1163 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1163_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1164 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1164_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1165 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1165_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1166 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1166_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1167 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1167_pos at_branch .Cbridge4 at_window returnWindow187 with_member window187_mem box((433/1024:ℝ),(217/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1168 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1168_pos at_branch .Cbridge4 at_window returnWindow187 with_member window187_mem box((433/1024:ℝ),(217/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1169 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1169_pos at_branch .old

theorem envelope_row1170 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1170_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1171 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1171_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1172 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1172_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1173 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1173_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1174 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1174_pos at_branch .Cbridge4 at_window returnWindow188 with_member window188_mem box((217/512:ℝ),(435/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1175 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1175_pos at_branch .Cbridge4 at_window returnWindow188 with_member window188_mem box((217/512:ℝ),(435/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1176 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1176_pos at_branch .old

theorem envelope_row1177 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1177_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1178 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1178_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1179 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1179_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1180 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1180_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1181 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1181_pos at_branch .Cbridge6 at_window returnWindow227 with_member window227_mem box((435/1024:ℝ),(109/256:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1182 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1182_pos at_branch .Cbridge6 at_window returnWindow227 with_member window227_mem box((435/1024:ℝ),(109/256:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1183 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1183_pos at_branch .old

theorem envelope_row1184 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1184_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1185 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1185_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1186 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1186_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1187 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1187_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1188 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1188_pos at_branch .Cbridge6 at_window returnWindow228 with_member window228_mem box((109/256:ℝ),(437/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1189 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1189_pos at_branch .Cbridge6 at_window returnWindow228 with_member window228_mem box((109/256:ℝ),(437/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1190 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1190_pos at_branch .old

theorem envelope_row1191 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1191_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1192 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1192_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1193 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1193_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1194 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1194_pos at_branch .Cbridge5 at_window returnWindow211 with_member window211_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1195 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1195_pos at_branch .Cbridge6 at_window returnWindow229 with_member window229_mem box((437/1024:ℝ),(219/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1196 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1196_pos at_branch .Cbridge6 at_window returnWindow229 with_member window229_mem box((437/1024:ℝ),(219/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1197 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1197_pos at_branch .old

theorem envelope_row1198 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1198_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1199 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1199_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1200 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1200_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1201 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1201_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1202 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1202_pos at_branch .Cbridge6 at_window returnWindow230 with_member window230_mem box((219/512:ℝ),(439/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1203 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1203_pos at_branch .Cbridge6 at_window returnWindow230 with_member window230_mem box((219/512:ℝ),(439/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1204 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1204_pos at_branch .old

theorem envelope_row1205 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1205_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1206 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1206_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1207 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1207_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1208 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1208_pos at_branch .Pwide at_window returnWindow93 with_member window93_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1209 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1209_pos at_branch .Cbridge4 at_window returnWindow193 with_member window193_mem box((439/1024:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1210 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1210_pos at_branch .Cbridge4 at_window returnWindow193 with_member window193_mem box((439/1024:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1211 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1211_pos at_branch .old

theorem envelope_row1212 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1212_pos at_branch .Cbridge0 at_window returnWindow103 with_member window103_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1213 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1213_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1214 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1214_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1215 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1215_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1216 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1216_pos at_branch .Cbridge4 at_window returnWindow194 with_member window194_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1217 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1217_pos at_branch .Cbridge4 at_window returnWindow194 with_member window194_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1218 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1218_pos at_branch .old

theorem envelope_row1219 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1219_pos at_branch .Cbridge0 at_window returnWindow103 with_member window103_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1220 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1220_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1221 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1221_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1222 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1222_pos at_branch .Pwide at_window returnWindow94 with_member window94_mem box((55/128:ℝ),(7/16:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1223 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1223_pos at_branch .Cbridge4 at_window returnWindow194 with_member window194_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1224 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1224_pos at_branch .Cbridge4 at_window returnWindow194 with_member window194_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1225 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1225_pos at_branch .old

theorem envelope_row1226 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1226_pos at_branch .Cbridge0 at_window returnWindow104 with_member window104_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1227 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1227_pos at_branch .Cbridge1 at_window returnWindow130 with_member window130_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1228 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1228_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1229 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1229_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1230 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1230_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1231 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1231_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1232 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1232_pos at_branch .old

theorem envelope_row1233 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1233_pos at_branch .Cbridge0 at_window returnWindow104 with_member window104_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1234 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1234_pos at_branch .Cbridge1 at_window returnWindow130 with_member window130_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1235 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1235_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1236 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1236_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1237 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1237_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1238 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1238_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1239 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1239_pos at_branch .old

theorem envelope_row1240 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1240_pos at_branch .Cbridge0 at_window returnWindow104 with_member window104_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1241 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1241_pos at_branch .Cphys at_window returnWindow11 with_member window11_mem box((3/8:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1242 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1242_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1243 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1243_pos at_branch .Pwide at_window returnWindow95 with_member window95_mem box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1244 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1244_pos at_branch .Cbridge5 at_window returnWindow213 with_member window213_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1245 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1245_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1246 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1246_pos at_branch .old

theorem envelope_row1247 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1247_pos at_branch .Cbridge0 at_window returnWindow105 with_member window105_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1248 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1248_pos at_branch .Cphys at_window returnWindow11 with_member window11_mem box((3/8:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1249 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1249_pos at_branch .Cbridge2 at_window returnWindow154 with_member window154_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1250 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1250_pos at_branch .Cbridge3 at_window returnWindow174 with_member window174_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1251 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1251_pos at_branch .Cbridge5 at_window returnWindow214 with_member window214_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1252 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1252_pos at_branch .Cbridge5 at_window returnWindow214 with_member window214_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1253 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1253_pos at_branch .old

theorem envelope_row1254 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1254_pos at_branch .Cbridge0 at_window returnWindow106 with_member window106_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1255 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1255_pos at_branch .Cphys at_window returnWindow11 with_member window11_mem box((3/8:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1256 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1256_pos at_branch .Cbridge2 at_window returnWindow155 with_member window155_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1257 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1257_pos at_branch .Cbridge3 at_window returnWindow175 with_member window175_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1258 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1258_pos at_branch .Cbridge3 at_window returnWindow175 with_member window175_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1259 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1259_pos at_branch .Cbridge3 at_window returnWindow175 with_member window175_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1260 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1260_pos at_branch .old

theorem envelope_row1261 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1261_pos at_branch .Cbridge0 at_window returnWindow107 with_member window107_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1262 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1262_pos at_branch .Cphys at_window returnWindow11 with_member window11_mem box((3/8:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1263 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1263_pos at_branch .Cbridge2 at_window returnWindow156 with_member window156_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1264 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1264_pos at_branch .Cbridge2 at_window returnWindow156 with_member window156_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1265 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1265_pos at_branch .Cbridge3 at_window returnWindow176 with_member window176_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1266 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1266_pos at_branch .Cbridge3 at_window returnWindow176 with_member window176_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1267 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1267_pos at_branch .old

theorem envelope_row1268 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1268_pos at_branch .Cbridge0 at_window returnWindow108 with_member window108_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1269 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1269_pos at_branch .Cbridge0 at_window returnWindow108 with_member window108_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1270 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1270_pos at_branch .Cbridge1 at_window returnWindow134 with_member window134_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1271 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1271_pos at_branch .Cbridge2 at_window returnWindow157 with_member window157_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1272 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1272_pos at_branch .Cbridge3 at_window returnWindow177 with_member window177_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1273 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1273_pos at_branch .Cbridge3 at_window returnWindow177 with_member window177_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1274 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1274_pos at_branch .old

theorem envelope_row1275 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1275_pos at_branch .Cbridge0 at_window returnWindow109 with_member window109_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1276 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1276_pos at_branch .Cbridge0 at_window returnWindow109 with_member window109_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1277 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1277_pos at_branch .Cbridge1 at_window returnWindow135 with_member window135_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1278 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1278_pos at_branch .Cbridge2 at_window returnWindow158 with_member window158_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1279 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1279_pos at_branch .Cbridge3 at_window returnWindow178 with_member window178_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1280 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1280_pos at_branch .Cbridge3 at_window returnWindow178 with_member window178_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1281 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1281_pos at_branch .old

theorem envelope_row1282 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1282_pos at_branch .Cbridge0 at_window returnWindow110 with_member window110_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1283 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1283_pos at_branch .Cbridge0 at_window returnWindow110 with_member window110_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1284 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1284_pos at_branch .Cbridge1 at_window returnWindow136 with_member window136_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1285 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1285_pos at_branch .Cbridge2 at_window returnWindow159 with_member window159_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1286 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1286_pos at_branch .Cbridge2 at_window returnWindow159 with_member window159_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1287 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1287_pos at_branch .Cbridge2 at_window returnWindow159 with_member window159_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1288 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1288_pos at_branch .old

theorem envelope_row1289 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1289_pos at_branch .Cbridge0 at_window returnWindow111 with_member window111_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1290 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1290_pos at_branch .Cbridge0 at_window returnWindow111 with_member window111_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1291 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1291_pos at_branch .Cbridge1 at_window returnWindow137 with_member window137_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1292 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1292_pos at_branch .Cbridge2 at_window returnWindow160 with_member window160_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1293 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1293_pos at_branch .Cbridge2 at_window returnWindow160 with_member window160_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1294 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1294_pos at_branch .Cbridge2 at_window returnWindow160 with_member window160_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1295 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1295_pos at_branch .old

theorem envelope_row1296 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1296_pos at_branch .Cbridge0 at_window returnWindow112 with_member window112_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1297 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1297_pos at_branch .Cbridge0 at_window returnWindow112 with_member window112_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1298 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1298_pos at_branch .Cbridge1 at_window returnWindow138 with_member window138_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1299 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1299_pos at_branch .Cbridge2 at_window returnWindow161 with_member window161_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1300 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1300_pos at_branch .Cbridge2 at_window returnWindow161 with_member window161_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1301 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1301_pos at_branch .Cbridge2 at_window returnWindow161 with_member window161_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1302 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1302_pos at_branch .old

theorem envelope_row1303 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1303_pos at_branch .Cbridge0 at_window returnWindow113 with_member window113_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1304 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1304_pos at_branch .Cbridge0 at_window returnWindow113 with_member window113_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1305 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1305_pos at_branch .Cbridge1 at_window returnWindow139 with_member window139_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1306 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1306_pos at_branch .Cbridge1 at_window returnWindow139 with_member window139_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1307 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1307_pos at_branch .Cbridge2 at_window returnWindow162 with_member window162_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1308 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1308_pos at_branch .Cbridge2 at_window returnWindow162 with_member window162_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1309 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1309_pos at_branch .old

theorem envelope_row1310 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1310_pos at_branch .Cbridge0 at_window returnWindow114 with_member window114_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1311 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1311_pos at_branch .Cbridge0 at_window returnWindow114 with_member window114_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1312 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1312_pos at_branch .Cphys at_window returnWindow75 with_member window75_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1313 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1313_pos at_branch .Cbridge1 at_window returnWindow140 with_member window140_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1314 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1314_pos at_branch .Cbridge2 at_window returnWindow163 with_member window163_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1315 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1315_pos at_branch .Cbridge2 at_window returnWindow163 with_member window163_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1316 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1316_pos at_branch .old

theorem envelope_row1317 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1317_pos at_branch .Cbridge0 at_window returnWindow115 with_member window115_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1318 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1318_pos at_branch .Cbridge0 at_window returnWindow115 with_member window115_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1319 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1319_pos at_branch .Cphys at_window returnWindow76 with_member window76_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1320 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1320_pos at_branch .Cbridge1 at_window returnWindow141 with_member window141_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1321 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1321_pos at_branch .Cbridge1 at_window returnWindow141 with_member window141_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1322 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1322_pos at_branch .Cbridge1 at_window returnWindow141 with_member window141_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1323 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1323_pos at_branch .old

theorem envelope_row1324 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1324_pos at_branch .Cbridge0 at_window returnWindow116 with_member window116_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1325 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1325_pos at_branch .Cbridge0 at_window returnWindow116 with_member window116_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1326 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1326_pos at_branch .Cphys at_window returnWindow77 with_member window77_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1327 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1327_pos at_branch .Cbridge1 at_window returnWindow142 with_member window142_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1328 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1328_pos at_branch .Cbridge1 at_window returnWindow142 with_member window142_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1329 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1329_pos at_branch .Cbridge1 at_window returnWindow142 with_member window142_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1330 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1330_pos at_branch .old

theorem envelope_row1331 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1331_pos at_branch .Cbridge0 at_window returnWindow117 with_member window117_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1332 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1332_pos at_branch .Cbridge0 at_window returnWindow117 with_member window117_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1333 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1333_pos at_branch .Cbridge0 at_window returnWindow117 with_member window117_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1334 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1334_pos at_branch .Cphys at_window returnWindow78 with_member window78_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1335 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1335_pos at_branch .Cphys at_window returnWindow78 with_member window78_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1336 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_window hδ, hp using row1336_pos at_branch .Cphys at_window returnWindow78 with_member window78_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1337 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1337_pos at_branch .old

theorem envelope_row1338 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1338_pos at_branch .old

theorem envelope_row1339 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1339_pos at_branch .old

theorem envelope_row1340 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1340_pos at_branch .old

theorem envelope_row1341 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1341_pos at_branch .old

theorem envelope_row1342 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1342_pos at_branch .old

theorem envelope_row1343 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newSwitch δ p := by
  return_old hδ, hp using row1343_pos at_branch .old

theorem envelope_row1344 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1344_pos at_branch .old

theorem envelope_row1345 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1345_pos at_branch .old

theorem envelope_row1346 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1346_pos at_branch .old

theorem envelope_row1347 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1347_pos at_branch .old

theorem envelope_row1348 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1348_pos at_branch .old

theorem envelope_row1349 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1349_pos at_branch .old

theorem envelope_row1350 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1350_pos at_branch .old

theorem envelope_row1351 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1351_pos at_branch .old

theorem envelope_row1352 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1352_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1353 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1353_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1354 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1354_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1355 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1355_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1356 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1356_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1357 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (5/16:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1357_pos at_branch .Pnew at_window returnWindow01 with_member window01_mem box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1358 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1358_pos at_branch .old

theorem envelope_row1359 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1359_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1360 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1360_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1361 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1361_pos at_branch .Pwide at_window returnWindow79 with_member window79_mem box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1362 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1362_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1363 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1363_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1364 {δ p : ℝ} (hδ : δ ∈ Set.Icc (5/16:ℝ) (41/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1364_pos at_branch .Pcountmid at_window returnWindow264 with_member window264_mem box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1365 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1365_pos at_branch .old

theorem envelope_row1366 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1366_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1367 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1367_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1368 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1368_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1369 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1369_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1370 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1370_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1371 {δ p : ℝ} (hδ : δ ∈ Set.Icc (41/128:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1371_pos at_branch .Pcount at_window returnWindow247 with_member window247_mem box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1372 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1372_pos at_branch .old

theorem envelope_row1373 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1373_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1374 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1374_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1375 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1375_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1376 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1376_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1377 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1377_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1378 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1378_pos at_branch .Pcount at_window returnWindow248 with_member window248_mem box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1379 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1379_pos at_branch .old

theorem envelope_row1380 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1380_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1381 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1381_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1382 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1382_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1383 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1383_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1384 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1384_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1385 {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (11/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1385_pos at_branch .Pcount at_window returnWindow249 with_member window249_mem box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1386 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1386_pos at_branch .old

theorem envelope_row1387 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1387_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1388 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1388_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1389 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1389_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1390 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1390_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1391 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1391_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1392 {δ p : ℝ} (hδ : δ ∈ Set.Icc (11/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1392_pos at_branch .Pcount at_window returnWindow250 with_member window250_mem box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1393 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1393_pos at_branch .old

theorem envelope_row1394 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1394_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1395 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1395_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1396 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1396_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1397 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1397_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1398 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1398_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1399 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (23/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1399_pos at_branch .Pcount at_window returnWindow251 with_member window251_mem box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1400 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1400_pos at_branch .old

theorem envelope_row1401 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1401_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1402 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1402_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1403 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1403_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1404 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1404_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1405 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1405_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1406 {δ p : ℝ} (hδ : δ ∈ Set.Icc (23/64:ℝ) (47/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1406_pos at_branch .Pcount at_window returnWindow252 with_member window252_mem box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1407 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1407_pos at_branch .old

theorem envelope_row1408 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1408_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1409 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1409_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1410 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1410_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1411 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1411_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1412 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1412_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1413 {δ p : ℝ} (hδ : δ ∈ Set.Icc (47/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1413_pos at_branch .Pcount at_window returnWindow253 with_member window253_mem box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1414 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1414_pos at_branch .old

theorem envelope_row1415 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1415_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1416 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1416_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1417 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1417_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1418 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1418_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1419 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1419_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1420 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (49/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1420_pos at_branch .Pcount at_window returnWindow254 with_member window254_mem box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1421 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1421_pos at_branch .old

theorem envelope_row1422 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1422_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1423 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1423_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1424 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1424_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1425 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1425_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1426 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1426_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1427 {δ p : ℝ} (hδ : δ ∈ Set.Icc (49/128:ℝ) (25/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1427_pos at_branch .Pcount at_window returnWindow255 with_member window255_mem box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1428 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1428_pos at_branch .old

theorem envelope_row1429 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1429_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1430 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1430_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1431 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1431_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1432 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1432_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1433 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1433_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1434 {δ p : ℝ} (hδ : δ ∈ Set.Icc (25/64:ℝ) (401/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1434_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1435 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1435_pos at_branch .old

theorem envelope_row1436 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1436_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1437 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1437_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1438 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1438_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1439 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1439_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1440 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1440_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1441 {δ p : ℝ} (hδ : δ ∈ Set.Icc (401/1024:ℝ) (201/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1441_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1442 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1442_pos at_branch .old

theorem envelope_row1443 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1443_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1444 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1444_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1445 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1445_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1446 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1446_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1447 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1447_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1448 {δ p : ℝ} (hδ : δ ∈ Set.Icc (201/512:ℝ) (403/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1448_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1449 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1449_pos at_branch .old

theorem envelope_row1450 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1450_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1451 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1451_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1452 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1452_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1453 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1453_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1454 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1454_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1455 {δ p : ℝ} (hδ : δ ∈ Set.Icc (403/1024:ℝ) (101/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1455_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1456 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1456_pos at_branch .old

theorem envelope_row1457 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1457_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1458 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1458_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1459 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1459_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1460 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1460_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1461 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1461_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1462 {δ p : ℝ} (hδ : δ ∈ Set.Icc (101/256:ℝ) (405/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1462_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1463 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1463_pos at_branch .old

theorem envelope_row1464 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1464_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1465 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1465_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1466 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1466_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1467 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1467_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1468 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1468_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1469 {δ p : ℝ} (hδ : δ ∈ Set.Icc (405/1024:ℝ) (203/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1469_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1470 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1470_pos at_branch .old

theorem envelope_row1471 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1471_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1472 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1472_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1473 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1473_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1474 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1474_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1475 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1475_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1476 {δ p : ℝ} (hδ : δ ∈ Set.Icc (203/512:ℝ) (407/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1476_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1477 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1477_pos at_branch .old

theorem envelope_row1478 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1478_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1479 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1479_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1480 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1480_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1481 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1481_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1482 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1482_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1483 {δ p : ℝ} (hδ : δ ∈ Set.Icc (407/1024:ℝ) (51/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1483_pos at_branch .Pcount at_window returnWindow256 with_member window256_mem box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1484 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1484_pos at_branch .old

theorem envelope_row1485 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1485_pos at_branch .Cbridge1 at_window returnWindow125 with_member window125_mem box((51/128:ℝ),(13/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1486 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1486_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1487 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1487_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1488 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1488_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1489 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1489_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1490 {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (13/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1490_pos at_branch .Pcount at_window returnWindow257 with_member window257_mem box((51/128:ℝ),(13/32:ℝ),(7/16:ℝ),(1/2:ℝ))

theorem envelope_row1491 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1491_pos at_branch .old

theorem envelope_row1492 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1492_pos at_branch .Cbridge1 at_window returnWindow126 with_member window126_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1493 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1493_pos at_branch .Cbridge1 at_window returnWindow126 with_member window126_mem box((13/32:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1494 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1494_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1495 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1495_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1496 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1496_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1497 {δ p : ℝ} (hδ : δ ∈ Set.Icc (13/32:ℝ) (417/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1497_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1498 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1498_pos at_branch .old

theorem envelope_row1499 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1499_pos at_branch .Cbridge2 at_window returnWindow143 with_member window143_mem box((417/1024:ℝ),(209/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1500 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1500_pos at_branch .Cbridge2 at_window returnWindow143 with_member window143_mem box((417/1024:ℝ),(209/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1501 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1501_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1502 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1502_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1503 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1503_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1504 {δ p : ℝ} (hδ : δ ∈ Set.Icc (417/1024:ℝ) (209/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1504_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1505 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1505_pos at_branch .old

theorem envelope_row1506 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1506_pos at_branch .Cbridge2 at_window returnWindow144 with_member window144_mem box((209/512:ℝ),(419/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1507 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1507_pos at_branch .Cbridge2 at_window returnWindow144 with_member window144_mem box((209/512:ℝ),(419/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1508 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1508_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1509 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1509_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1510 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1510_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1511 {δ p : ℝ} (hδ : δ ∈ Set.Icc (209/512:ℝ) (419/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1511_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1512 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1512_pos at_branch .old

theorem envelope_row1513 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1513_pos at_branch .Cbridge2 at_window returnWindow145 with_member window145_mem box((419/1024:ℝ),(105/256:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1514 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1514_pos at_branch .Cbridge2 at_window returnWindow145 with_member window145_mem box((419/1024:ℝ),(105/256:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1515 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1515_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1516 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1516_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1517 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1517_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1518 {δ p : ℝ} (hδ : δ ∈ Set.Icc (419/1024:ℝ) (105/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1518_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1519 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1519_pos at_branch .old

theorem envelope_row1520 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1520_pos at_branch .Cbridge2 at_window returnWindow146 with_member window146_mem box((105/256:ℝ),(421/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1521 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1521_pos at_branch .Cbridge2 at_window returnWindow146 with_member window146_mem box((105/256:ℝ),(421/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1522 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1522_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1523 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1523_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1524 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1524_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1525 {δ p : ℝ} (hδ : δ ∈ Set.Icc (105/256:ℝ) (421/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1525_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1526 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1526_pos at_branch .old

theorem envelope_row1527 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1527_pos at_branch .Cbridge2 at_window returnWindow147 with_member window147_mem box((421/1024:ℝ),(211/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1528 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1528_pos at_branch .Cbridge2 at_window returnWindow147 with_member window147_mem box((421/1024:ℝ),(211/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1529 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1529_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1530 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1530_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1531 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1531_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1532 {δ p : ℝ} (hδ : δ ∈ Set.Icc (421/1024:ℝ) (211/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1532_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1533 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1533_pos at_branch .old

theorem envelope_row1534 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1534_pos at_branch .Cbridge2 at_window returnWindow148 with_member window148_mem box((211/512:ℝ),(423/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1535 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1535_pos at_branch .Cbridge2 at_window returnWindow148 with_member window148_mem box((211/512:ℝ),(423/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1536 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1536_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1537 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1537_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1538 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1538_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1539 {δ p : ℝ} (hδ : δ ∈ Set.Icc (211/512:ℝ) (423/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1539_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1540 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1540_pos at_branch .old

theorem envelope_row1541 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1541_pos at_branch .Cbridge2 at_window returnWindow149 with_member window149_mem box((423/1024:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1542 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1542_pos at_branch .Cbridge2 at_window returnWindow149 with_member window149_mem box((423/1024:ℝ),(53/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1543 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1543_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1544 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1544_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1545 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1545_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1546 {δ p : ℝ} (hδ : δ ∈ Set.Icc (423/1024:ℝ) (53/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1546_pos at_branch .Pcount at_window returnWindow258 with_member window258_mem box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1547 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1547_pos at_branch .old

theorem envelope_row1548 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1548_pos at_branch .Cbridge2 at_window returnWindow150 with_member window150_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1549 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1549_pos at_branch .Cbridge2 at_window returnWindow150 with_member window150_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1550 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1550_pos at_branch .Pcountmid at_window returnWindow277 with_member window277_mem box((53/128:ℝ),(425/1024:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1551 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1551_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1552 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1552_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1553 {δ p : ℝ} (hδ : δ ∈ Set.Icc (53/128:ℝ) (425/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1553_pos at_branch .Pcount at_window returnWindow259 with_member window259_mem box((53/128:ℝ),(425/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1554 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1554_pos at_branch .old

theorem envelope_row1555 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1555_pos at_branch .Cbridge2 at_window returnWindow150 with_member window150_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1556 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1556_pos at_branch .Cbridge2 at_window returnWindow150 with_member window150_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1557 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1557_pos at_branch .Pcountmid at_window returnWindow278 with_member window278_mem box((425/1024:ℝ),(213/512:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1558 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1558_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1559 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1559_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1560 {δ p : ℝ} (hδ : δ ∈ Set.Icc (425/1024:ℝ) (213/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1560_pos at_branch .Pcount at_window returnWindow260 with_member window260_mem box((425/1024:ℝ),(213/512:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1561 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1561_pos at_branch .old

theorem envelope_row1562 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1562_pos at_branch .Cbridge2 at_window returnWindow150 with_member window150_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1563 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1563_pos at_branch .Cbridge2 at_window returnWindow150 with_member window150_mem box((53/128:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1564 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1564_pos at_branch .Pcountmid at_window returnWindow279 with_member window279_mem box((213/512:ℝ),(427/1024:ℝ),(15/32:ℝ),(1/2:ℝ))

theorem envelope_row1565 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1565_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1566 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1566_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1567 {δ p : ℝ} (hδ : δ ∈ Set.Icc (213/512:ℝ) (427/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1567_pos at_branch .Pcount at_window returnWindow261 with_member window261_mem box((213/512:ℝ),(427/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1568 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1568_pos at_branch .old

theorem envelope_row1569 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1569_pos at_branch .Cbridge3 at_window returnWindow166 with_member window166_mem box((427/1024:ℝ),(107/256:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1570 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1570_pos at_branch .Cbridge3 at_window returnWindow166 with_member window166_mem box((427/1024:ℝ),(107/256:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1571 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1571_pos at_branch .Cbridge3 at_window returnWindow166 with_member window166_mem box((427/1024:ℝ),(107/256:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1572 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1572_pos at_branch .Pcountmid at_window returnWindow280 with_member window280_mem box((427/1024:ℝ),(107/256:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1573 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1573_pos at_branch .Pcount at_window returnWindow262 with_member window262_mem box((427/1024:ℝ),(107/256:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row1574 {δ p : ℝ} (hδ : δ ∈ Set.Icc (427/1024:ℝ) (107/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1574_pos at_branch .Pcount at_window returnWindow262 with_member window262_mem box((427/1024:ℝ),(107/256:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row1575 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1575_pos at_branch .old

theorem envelope_row1576 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1576_pos at_branch .Cbridge3 at_window returnWindow167 with_member window167_mem box((107/256:ℝ),(429/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1577 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1577_pos at_branch .Cbridge3 at_window returnWindow167 with_member window167_mem box((107/256:ℝ),(429/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1578 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1578_pos at_branch .Cbridge3 at_window returnWindow167 with_member window167_mem box((107/256:ℝ),(429/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1579 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1579_pos at_branch .Pcountmid at_window returnWindow281 with_member window281_mem box((107/256:ℝ),(429/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1580 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1580_pos at_branch .Pcountmid at_window returnWindow281 with_member window281_mem box((107/256:ℝ),(429/1024:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1581 {δ p : ℝ} (hδ : δ ∈ Set.Icc (107/256:ℝ) (429/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1581_pos at_branch .Pcount at_window returnWindow263 with_member window263_mem box((107/256:ℝ),(429/1024:ℝ),(127/256:ℝ),(1/2:ℝ))

theorem envelope_row1582 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1582_pos at_branch .old

theorem envelope_row1583 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1583_pos at_branch .Cbridge3 at_window returnWindow168 with_member window168_mem box((429/1024:ℝ),(215/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1584 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1584_pos at_branch .Cbridge3 at_window returnWindow168 with_member window168_mem box((429/1024:ℝ),(215/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1585 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1585_pos at_branch .Cbridge3 at_window returnWindow168 with_member window168_mem box((429/1024:ℝ),(215/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1586 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1586_pos at_branch .Cbridge3 at_window returnWindow168 with_member window168_mem box((429/1024:ℝ),(215/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1587 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1587_pos at_branch .Pcountmid at_window returnWindow282 with_member window282_mem box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row1588 {δ p : ℝ} (hδ : δ ∈ Set.Icc (429/1024:ℝ) (215/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1588_pos at_branch .Pcountmid at_window returnWindow282 with_member window282_mem box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ))

theorem envelope_row1589 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1589_pos at_branch .old

theorem envelope_row1590 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1590_pos at_branch .Cnew at_window returnWindow51 with_member window51_mem box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1591 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1591_pos at_branch .Cnew at_window returnWindow51 with_member window51_mem box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1592 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1592_pos at_branch .Cnew at_window returnWindow51 with_member window51_mem box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1593 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1593_pos at_branch .Cnew at_window returnWindow51 with_member window51_mem box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1594 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1594_pos at_branch .Cnew at_window returnWindow51 with_member window51_mem box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1595 {δ p : ℝ} (hδ : δ ∈ Set.Icc (215/512:ℝ) (431/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1595_pos at_branch .Cnew at_window returnWindow51 with_member window51_mem box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1596 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1596_pos at_branch .old

theorem envelope_row1597 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1597_pos at_branch .Cnew at_window returnWindow52 with_member window52_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1598 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1598_pos at_branch .Cnew at_window returnWindow52 with_member window52_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1599 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1599_pos at_branch .Cnew at_window returnWindow52 with_member window52_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1600 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1600_pos at_branch .Cnew at_window returnWindow52 with_member window52_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1601 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1601_pos at_branch .Cnew at_window returnWindow52 with_member window52_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1602 {δ p : ℝ} (hδ : δ ∈ Set.Icc (431/1024:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1602_pos at_branch .Cnew at_window returnWindow52 with_member window52_mem box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1603 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1603_pos at_branch .old

theorem envelope_row1604 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1604_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1605 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1605_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1606 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1606_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1607 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1607_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1608 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1608_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1609 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (433/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1609_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1610 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1610_pos at_branch .old

theorem envelope_row1611 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1611_pos at_branch .Cbridge4 at_window returnWindow187 with_member window187_mem box((433/1024:ℝ),(217/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1612 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1612_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1613 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1613_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1614 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1614_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1615 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1615_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1616 {δ p : ℝ} (hδ : δ ∈ Set.Icc (433/1024:ℝ) (217/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1616_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1617 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1617_pos at_branch .old

theorem envelope_row1618 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1618_pos at_branch .Cbridge4 at_window returnWindow188 with_member window188_mem box((217/512:ℝ),(435/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1619 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1619_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1620 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1620_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1621 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1621_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1622 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1622_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1623 {δ p : ℝ} (hδ : δ ∈ Set.Icc (217/512:ℝ) (435/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1623_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1624 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1624_pos at_branch .old

theorem envelope_row1625 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1625_pos at_branch .Cbridge6 at_window returnWindow227 with_member window227_mem box((435/1024:ℝ),(109/256:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1626 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1626_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1627 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1627_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1628 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1628_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1629 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1629_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1630 {δ p : ℝ} (hδ : δ ∈ Set.Icc (435/1024:ℝ) (109/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1630_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1631 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1631_pos at_branch .old

theorem envelope_row1632 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1632_pos at_branch .Cbridge6 at_window returnWindow228 with_member window228_mem box((109/256:ℝ),(437/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1633 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1633_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1634 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1634_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1635 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1635_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1636 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1636_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1637 {δ p : ℝ} (hδ : δ ∈ Set.Icc (109/256:ℝ) (437/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1637_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1638 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1638_pos at_branch .old

theorem envelope_row1639 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1639_pos at_branch .Cbridge4 at_window returnWindow191 with_member window191_mem box((437/1024:ℝ),(219/512:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1640 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1640_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1641 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1641_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1642 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1642_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1643 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1643_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1644 {δ p : ℝ} (hδ : δ ∈ Set.Icc (437/1024:ℝ) (219/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1644_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1645 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1645_pos at_branch .old

theorem envelope_row1646 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1646_pos at_branch .Cbridge4 at_window returnWindow192 with_member window192_mem box((219/512:ℝ),(439/1024:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1647 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1647_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1648 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1648_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1649 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1649_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1650 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1650_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1651 {δ p : ℝ} (hδ : δ ∈ Set.Icc (219/512:ℝ) (439/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1651_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1652 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1652_pos at_branch .old

theorem envelope_row1653 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1653_pos at_branch .Cbridge4 at_window returnWindow193 with_member window193_mem box((439/1024:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1654 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1654_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1655 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1655_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1656 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1656_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1657 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1657_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1658 {δ p : ℝ} (hδ : δ ∈ Set.Icc (439/1024:ℝ) (55/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1658_pos at_branch .Cnew at_window returnWindow53 with_member window53_mem box((27/64:ℝ),(55/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1659 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1659_pos at_branch .old

theorem envelope_row1660 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1660_pos at_branch .Cbridge4 at_window returnWindow194 with_member window194_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1661 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1661_pos at_branch .Cnew at_window returnWindow54 with_member window54_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1662 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1662_pos at_branch .Cnew at_window returnWindow54 with_member window54_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1663 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1663_pos at_branch .Cnew at_window returnWindow54 with_member window54_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1664 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1664_pos at_branch .Cnew at_window returnWindow54 with_member window54_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1665 {δ p : ℝ} (hδ : δ ∈ Set.Icc (55/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1665_pos at_branch .Cnew at_window returnWindow54 with_member window54_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1666 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1666_pos at_branch .old

theorem envelope_row1667 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1667_pos at_branch .Cbridge4 at_window returnWindow194 with_member window194_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1668 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1668_pos at_branch .Cbridge6 at_window returnWindow232 with_member window232_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1669 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1669_pos at_branch .Cnew at_window returnWindow54 with_member window54_mem box((55/128:ℝ),(7/16:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1670 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1670_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1671 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1671_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1672 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (255/512:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1672_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1673 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (255/512:ℝ) (511/1024:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1673_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1674 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (511/1024:ℝ) (1023/2048:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1674_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1675 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (1023/2048:ℝ) (2047/4096:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1675_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1676 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (223/512:ℝ))
    (hp : p ∈ Set.Icc (2047/4096:ℝ) (4095/8192:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1676_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1677 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (223/512:ℝ))
    (hp : p ∈ Set.Icc (4095/8192:ℝ) (8191/16384:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1677_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1678 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (445/1024:ℝ))
    (hp : p ∈ Set.Icc (8191/16384:ℝ) (16383/32768:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1678_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1679 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (445/1024:ℝ))
    (hp : p ∈ Set.Icc (16383/32768:ℝ) (32767/65536:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1679_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1680 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (889/2048:ℝ))
    (hp : p ∈ Set.Icc (32767/65536:ℝ) (65535/131072:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1680_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1681 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (889/2048:ℝ))
    (hp : p ∈ Set.Icc (65535/131072:ℝ) (131071/262144:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1681_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1682 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (1777/4096:ℝ))
    (hp : p ∈ Set.Icc (131071/262144:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1682_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1683 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1777/4096:ℝ) (889/2048:ℝ))
    (hp : p ∈ Set.Icc (131071/262144:ℝ) (262143/524288:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1683_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1684 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1777/4096:ℝ) (889/2048:ℝ))
    (hp : p ∈ Set.Icc (262143/524288:ℝ) (524287/1048576:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1684_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1685 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1777/4096:ℝ) (889/2048:ℝ))
    (hp : p ∈ Set.Icc (524287/1048576:ℝ) (1048575/2097152:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1685_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1686 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1777/4096:ℝ) (3555/8192:ℝ))
    (hp : p ∈ Set.Icc (1048575/2097152:ℝ) (2097151/4194304:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1686_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1687 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1777/4096:ℝ) (7109/16384:ℝ))
    (hp : p ∈ Set.Icc (2097151/4194304:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1687_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1688 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7109/16384:ℝ) (3555/8192:ℝ))
    (hp : p ∈ Set.Icc (2097151/4194304:ℝ) (4194303/8388608:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1688_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1689 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7109/16384:ℝ) (3555/8192:ℝ))
    (hp : p ∈ Set.Icc (4194303/8388608:ℝ) (8388607/16777216:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1689_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1690 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7109/16384:ℝ) (3555/8192:ℝ))
    (hp : p ∈ Set.Icc (8388607/16777216:ℝ) (16777215/33554432:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1690_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1691 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7109/16384:ℝ) (14219/32768:ℝ))
    (hp : p ∈ Set.Icc (16777215/33554432:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1691_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1692 {δ p : ℝ} (hδ : δ ∈ Set.Icc (14219/32768:ℝ) (3555/8192:ℝ))
    (hp : p ∈ Set.Icc (16777215/33554432:ℝ) (33554431/67108864:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1692_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1693 {δ p : ℝ} (hδ : δ ∈ Set.Icc (14219/32768:ℝ) (227505/524288:ℝ))
    (hp : p ∈ Set.Icc (33554431/67108864:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1693_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1694 {δ p : ℝ} (hδ : δ ∈ Set.Icc (227505/524288:ℝ) (113753/262144:ℝ))
    (hp : p ∈ Set.Icc (33554431/67108864:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1694_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1695 {δ p : ℝ} (hδ : δ ∈ Set.Icc (113753/262144:ℝ) (56877/131072:ℝ))
    (hp : p ∈ Set.Icc (33554431/67108864:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1695_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1696 {δ p : ℝ} (hδ : δ ∈ Set.Icc (56877/131072:ℝ) (28439/65536:ℝ))
    (hp : p ∈ Set.Icc (33554431/67108864:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1696_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1697 {δ p : ℝ} (hδ : δ ∈ Set.Icc (28439/65536:ℝ) (3555/8192:ℝ))
    (hp : p ∈ Set.Icc (33554431/67108864:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1697_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1698 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3555/8192:ℝ) (889/2048:ℝ))
    (hp : p ∈ Set.Icc (1048575/2097152:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1698_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1699 {δ p : ℝ} (hδ : δ ∈ Set.Icc (889/2048:ℝ) (445/1024:ℝ))
    (hp : p ∈ Set.Icc (32767/65536:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1699_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1700 {δ p : ℝ} (hδ : δ ∈ Set.Icc (445/1024:ℝ) (223/512:ℝ))
    (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1700_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1701 {δ p : ℝ} (hδ : δ ∈ Set.Icc (223/512:ℝ) (7/16:ℝ))
    (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1701_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1702 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1702_pos at_branch .old

theorem envelope_row1703 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1703_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1704 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1704_pos at_branch .Cbridge6 at_window returnWindow233 with_member window233_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1705 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1705_pos at_branch .Cbridge6 at_window returnWindow233 with_member window233_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1706 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1706_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1707 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1707_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1708 {δ p : ℝ} (hδ : δ ∈ Set.Icc (7/16:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1708_pos at_branch .Cnew at_window returnWindow03 with_member window03_mem box((111/256:ℝ),(57/128:ℝ),(31/64:ℝ),(1/2:ℝ))

theorem envelope_row1709 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1709_pos at_branch .old

theorem envelope_row1710 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1710_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1711 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1711_pos at_branch .Cbridge6 at_window returnWindow233 with_member window233_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1712 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1712_pos at_branch .Cbridge6 at_window returnWindow233 with_member window233_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1713 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1713_pos at_branch .Cbridge6 at_window returnWindow233 with_member window233_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1714 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1714_pos at_branch .Cbridge6 at_window returnWindow233 with_member window233_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1715 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1715_pos at_branch .Cbridge6 at_window returnWindow233 with_member window233_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1716 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1716_pos at_branch .old

theorem envelope_row1717 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1717_pos at_branch .Cbridge5 at_window returnWindow213 with_member window213_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1718 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1718_pos at_branch .Cbridge4 at_window returnWindow195 with_member window195_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1719 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1719_pos at_branch .Cbridge6 at_window returnWindow233 with_member window233_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1720 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1720_pos at_branch .Cbridge6 at_window returnWindow233 with_member window233_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1721 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1721_pos at_branch .Cbridge6 at_window returnWindow233 with_member window233_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1722 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1722_pos at_branch .Cbridge6 at_window returnWindow233 with_member window233_mem box((7/16:ℝ),(57/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1723 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1723_pos at_branch .old

theorem envelope_row1724 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1724_pos at_branch .Cbridge5 at_window returnWindow214 with_member window214_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1725 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1725_pos at_branch .Cbridge4 at_window returnWindow196 with_member window196_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1726 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1726_pos at_branch .Cbridge6 at_window returnWindow234 with_member window234_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1727 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1727_pos at_branch .Cbridge6 at_window returnWindow234 with_member window234_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1728 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1728_pos at_branch .Cbridge6 at_window returnWindow234 with_member window234_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1729 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (29/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1729_pos at_branch .Cbridge6 at_window returnWindow234 with_member window234_mem box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1730 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1730_pos at_branch .old

theorem envelope_row1731 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1731_pos at_branch .Cbridge5 at_window returnWindow215 with_member window215_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1732 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1732_pos at_branch .Cbridge4 at_window returnWindow197 with_member window197_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1733 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1733_pos at_branch .Cbridge4 at_window returnWindow197 with_member window197_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1734 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1734_pos at_branch .Cbridge4 at_window returnWindow197 with_member window197_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1735 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1735_pos at_branch .Cbridge4 at_window returnWindow197 with_member window197_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1736 {δ p : ℝ} (hδ : δ ∈ Set.Icc (29/64:ℝ) (59/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1736_pos at_branch .Cbridge4 at_window returnWindow197 with_member window197_mem box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1737 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1737_pos at_branch .old

theorem envelope_row1738 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1738_pos at_branch .Cbridge3 at_window returnWindow176 with_member window176_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1739 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1739_pos at_branch .Cbridge5 at_window returnWindow216 with_member window216_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1740 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1740_pos at_branch .Cbridge4 at_window returnWindow198 with_member window198_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1741 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1741_pos at_branch .Cbridge4 at_window returnWindow198 with_member window198_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1742 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1742_pos at_branch .Cbridge4 at_window returnWindow198 with_member window198_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1743 {δ p : ℝ} (hδ : δ ∈ Set.Icc (59/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1743_pos at_branch .Cbridge4 at_window returnWindow198 with_member window198_mem box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1744 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1744_pos at_branch .old

theorem envelope_row1745 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1745_pos at_branch .Cbridge3 at_window returnWindow177 with_member window177_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1746 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1746_pos at_branch .Cbridge5 at_window returnWindow217 with_member window217_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1747 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1747_pos at_branch .Cbridge5 at_window returnWindow217 with_member window217_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1748 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1748_pos at_branch .Cbridge5 at_window returnWindow217 with_member window217_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1749 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1749_pos at_branch .Cbridge5 at_window returnWindow217 with_member window217_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1750 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (61/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1750_pos at_branch .Cbridge5 at_window returnWindow217 with_member window217_mem box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1751 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1751_pos at_branch .old

theorem envelope_row1752 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1752_pos at_branch .Cbridge2 at_window returnWindow158 with_member window158_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1753 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1753_pos at_branch .Cbridge3 at_window returnWindow178 with_member window178_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1754 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1754_pos at_branch .Cbridge5 at_window returnWindow218 with_member window218_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1755 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1755_pos at_branch .Cbridge5 at_window returnWindow218 with_member window218_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1756 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1756_pos at_branch .Cbridge5 at_window returnWindow218 with_member window218_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1757 {δ p : ℝ} (hδ : δ ∈ Set.Icc (61/128:ℝ) (31/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1757_pos at_branch .Cbridge5 at_window returnWindow218 with_member window218_mem box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1758 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1758_pos at_branch .old

theorem envelope_row1759 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1759_pos at_branch .Cbridge2 at_window returnWindow159 with_member window159_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1760 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1760_pos at_branch .Cbridge3 at_window returnWindow179 with_member window179_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1761 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1761_pos at_branch .Cbridge3 at_window returnWindow179 with_member window179_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1762 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1762_pos at_branch .Cbridge3 at_window returnWindow179 with_member window179_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1763 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1763_pos at_branch .Cbridge3 at_window returnWindow179 with_member window179_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1764 {δ p : ℝ} (hδ : δ ∈ Set.Icc (31/64:ℝ) (63/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1764_pos at_branch .Cbridge3 at_window returnWindow179 with_member window179_mem box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1765 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1765_pos at_branch .old

theorem envelope_row1766 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1766_pos at_branch .Cbridge2 at_window returnWindow160 with_member window160_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1767 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1767_pos at_branch .Cbridge3 at_window returnWindow180 with_member window180_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1768 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1768_pos at_branch .Cbridge3 at_window returnWindow180 with_member window180_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1769 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1769_pos at_branch .Cbridge3 at_window returnWindow180 with_member window180_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1770 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1770_pos at_branch .Cbridge3 at_window returnWindow180 with_member window180_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1771 {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1771_pos at_branch .Cbridge3 at_window returnWindow180 with_member window180_mem box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1772 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1772_pos at_branch .old

theorem envelope_row1773 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1773_pos at_branch .Cbridge2 at_window returnWindow161 with_member window161_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1774 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1774_pos at_branch .Cbridge2 at_window returnWindow161 with_member window161_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1775 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1775_pos at_branch .Cbridge3 at_window returnWindow181 with_member window181_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1776 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1776_pos at_branch .Cbridge3 at_window returnWindow181 with_member window181_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1777 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1777_pos at_branch .Cbridge3 at_window returnWindow181 with_member window181_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1778 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1/2:ℝ) (65/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1778_pos at_branch .Cbridge3 at_window returnWindow181 with_member window181_mem box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1779 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1779_pos at_branch .old

theorem envelope_row1780 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1780_pos at_branch .Cbridge1 at_window returnWindow139 with_member window139_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1781 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1781_pos at_branch .Cbridge2 at_window returnWindow162 with_member window162_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1782 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1782_pos at_branch .Cbridge2 at_window returnWindow162 with_member window162_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1783 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1783_pos at_branch .Cbridge2 at_window returnWindow162 with_member window162_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1784 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1784_pos at_branch .Cbridge2 at_window returnWindow162 with_member window162_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1785 {δ p : ℝ} (hδ : δ ∈ Set.Icc (65/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1785_pos at_branch .Cbridge2 at_window returnWindow162 with_member window162_mem box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1786 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1786_pos at_branch .old

theorem envelope_row1787 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1787_pos at_branch .Cbridge1 at_window returnWindow140 with_member window140_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1788 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1788_pos at_branch .Cbridge2 at_window returnWindow163 with_member window163_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1789 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1789_pos at_branch .Cbridge2 at_window returnWindow163 with_member window163_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1790 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1790_pos at_branch .Cbridge2 at_window returnWindow163 with_member window163_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1791 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1791_pos at_branch .Cbridge2 at_window returnWindow163 with_member window163_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1792 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (67/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1792_pos at_branch .Cbridge2 at_window returnWindow163 with_member window163_mem box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1793 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1793_pos at_branch .old

theorem envelope_row1794 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1794_pos at_branch .Cbridge1 at_window returnWindow141 with_member window141_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1795 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1795_pos at_branch .Cbridge2 at_window returnWindow164 with_member window164_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1796 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1796_pos at_branch .Cbridge2 at_window returnWindow164 with_member window164_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1797 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1797_pos at_branch .Cbridge2 at_window returnWindow164 with_member window164_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1798 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1798_pos at_branch .Cbridge2 at_window returnWindow164 with_member window164_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1799 {δ p : ℝ} (hδ : δ ∈ Set.Icc (67/128:ℝ) (17/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1799_pos at_branch .Cbridge2 at_window returnWindow164 with_member window164_mem box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1800 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1800_pos at_branch .old

theorem envelope_row1801 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1801_pos at_branch .Cphys at_window returnWindow77 with_member window77_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1802 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1802_pos at_branch .Cbridge1 at_window returnWindow142 with_member window142_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1803 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1803_pos at_branch .Cbridge2 at_window returnWindow165 with_member window165_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1804 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1804_pos at_branch .Cbridge2 at_window returnWindow165 with_member window165_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1805 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1805_pos at_branch .Cbridge2 at_window returnWindow165 with_member window165_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1806 {δ p : ℝ} (hδ : δ ∈ Set.Icc (17/32:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1806_pos at_branch .Cbridge2 at_window returnWindow165 with_member window165_mem box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1807 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1807_pos at_branch .old

theorem envelope_row1808 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1808_pos at_branch .Cphys at_window returnWindow78 with_member window78_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1809 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1809_pos at_branch .Cphys at_window returnWindow78 with_member window78_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1810 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1810_pos at_branch .Cphys at_window returnWindow78 with_member window78_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1811 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1811_pos at_branch .Cphys at_window returnWindow78 with_member window78_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1812 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1812_pos at_branch .Cphys at_window returnWindow78 with_member window78_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1813 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (35/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_window hδ, hp using row1813_pos at_branch .Cbridge3 at_window returnWindow186 with_member window186_mem box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(1/2:ℝ))

theorem envelope_row1814 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1814_pos at_branch .old

theorem envelope_row1815 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1815_pos at_branch .old

theorem envelope_row1816 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1816_pos at_branch .old

theorem envelope_row1817 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1817_pos at_branch .old

theorem envelope_row1818 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1818_pos at_branch .old

theorem envelope_row1819 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1819_pos at_branch .old

theorem envelope_row1820 {δ p : ℝ} (hδ : δ ∈ Set.Icc (35/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : ReturnAt .newTop δ p := by
  return_old hδ, hp using row1820_pos at_branch .old

return_split cover_node_000 edge_at .oldSmall box((0:ℝ),(9/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row001 right_from envelope_row002

return_split cover_node_001 edge_at .oldSmall box((0:ℝ),(9/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row000 right_from cover_node_000

return_split cover_node_002 edge_at .oldSmall box((0:ℝ),(9/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row003 right_from envelope_row004

return_split cover_node_003 edge_at .oldSmall box((0:ℝ),(9/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row005 right_from envelope_row006

return_split cover_node_004 edge_at .oldSmall box((0:ℝ),(9/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_002 right_from cover_node_003

return_split cover_node_005 edge_at .oldSmall box((0:ℝ),(9/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_001 right_from cover_node_004

return_split cover_node_006 edge_at .oldSmall box((9/32:ℝ),(5/16:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row008 right_from envelope_row009

return_split cover_node_007 edge_at .oldSmall box((9/32:ℝ),(5/16:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row007 right_from cover_node_006

return_split cover_node_008 edge_at .oldSmall box((9/32:ℝ),(5/16:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row010 right_from envelope_row011

return_split cover_node_009 edge_at .oldSmall box((9/32:ℝ),(5/16:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row012 right_from envelope_row013

return_split cover_node_010 edge_at .oldSmall box((9/32:ℝ),(5/16:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_008 right_from cover_node_009

return_split cover_node_011 edge_at .oldSmall box((9/32:ℝ),(5/16:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_007 right_from cover_node_010

return_split cover_node_012 edge_at .oldSmall box((0:ℝ),(5/16:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (9/32:ℝ) left_from cover_node_005 right_from cover_node_011

return_split cover_node_013 edge_at .oldSmall box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row015 right_from envelope_row016

return_split cover_node_014 edge_at .oldSmall box((5/16:ℝ),(41/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row014 right_from cover_node_013

return_split cover_node_015 edge_at .oldSmall box((5/16:ℝ),(41/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row017 right_from envelope_row018

return_split cover_node_016 edge_at .oldSmall box((5/16:ℝ),(41/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row019 right_from envelope_row020

return_split cover_node_017 edge_at .oldSmall box((5/16:ℝ),(41/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_015 right_from cover_node_016

return_split cover_node_018 edge_at .oldSmall box((5/16:ℝ),(41/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_014 right_from cover_node_017

return_split cover_node_019 edge_at .oldSmall box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row022 right_from envelope_row023

return_split cover_node_020 edge_at .oldSmall box((41/128:ℝ),(21/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row021 right_from cover_node_019

return_split cover_node_021 edge_at .oldSmall box((41/128:ℝ),(21/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row024 right_from envelope_row025

return_split cover_node_022 edge_at .oldSmall box((41/128:ℝ),(21/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row026 right_from envelope_row027

return_split cover_node_023 edge_at .oldSmall box((41/128:ℝ),(21/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_021 right_from cover_node_022

return_split cover_node_024 edge_at .oldSmall box((41/128:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_020 right_from cover_node_023

return_split cover_node_025 edge_at .oldSmall box((5/16:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (41/128:ℝ) left_from cover_node_018 right_from cover_node_024

return_split cover_node_026 edge_at .oldSmall box((0:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (5/16:ℝ) left_from cover_node_012 right_from cover_node_025

return_split cover_node_027 edge_at .oldSmall box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row029 right_from envelope_row030

return_split cover_node_028 edge_at .oldSmall box((21/64:ℝ),(43/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row028 right_from cover_node_027

return_split cover_node_029 edge_at .oldSmall box((21/64:ℝ),(43/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row031 right_from envelope_row032

return_split cover_node_030 edge_at .oldSmall box((21/64:ℝ),(43/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row033 right_from envelope_row034

return_split cover_node_031 edge_at .oldSmall box((21/64:ℝ),(43/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_029 right_from cover_node_030

return_split cover_node_032 edge_at .oldSmall box((21/64:ℝ),(43/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_028 right_from cover_node_031

return_split cover_node_033 edge_at .oldSmall box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row036 right_from envelope_row037

return_split cover_node_034 edge_at .oldSmall box((43/128:ℝ),(11/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row035 right_from cover_node_033

return_split cover_node_035 edge_at .oldSmall box((43/128:ℝ),(11/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row038 right_from envelope_row039

return_split cover_node_036 edge_at .oldSmall box((43/128:ℝ),(11/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row040 right_from envelope_row041

return_split cover_node_037 edge_at .oldSmall box((43/128:ℝ),(11/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_035 right_from cover_node_036

return_split cover_node_038 edge_at .oldSmall box((43/128:ℝ),(11/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_034 right_from cover_node_037

return_split cover_node_039 edge_at .oldSmall box((21/64:ℝ),(11/32:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (43/128:ℝ) left_from cover_node_032 right_from cover_node_038

return_split cover_node_040 edge_at .oldSmall box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row043 right_from envelope_row044

return_split cover_node_041 edge_at .oldSmall box((11/32:ℝ),(45/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row042 right_from cover_node_040

return_split cover_node_042 edge_at .oldSmall box((11/32:ℝ),(45/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row045 right_from envelope_row046

return_split cover_node_043 edge_at .oldSmall box((11/32:ℝ),(45/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row047 right_from envelope_row048

return_split cover_node_044 edge_at .oldSmall box((11/32:ℝ),(45/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_042 right_from cover_node_043

return_split cover_node_045 edge_at .oldSmall box((11/32:ℝ),(45/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_041 right_from cover_node_044

return_split cover_node_046 edge_at .oldSmall box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row050 right_from envelope_row051

return_split cover_node_047 edge_at .oldSmall box((45/128:ℝ),(23/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row049 right_from cover_node_046

return_split cover_node_048 edge_at .oldSmall box((45/128:ℝ),(23/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row052 right_from envelope_row053

return_split cover_node_049 edge_at .oldSmall box((45/128:ℝ),(23/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row054 right_from envelope_row055

return_split cover_node_050 edge_at .oldSmall box((45/128:ℝ),(23/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_048 right_from cover_node_049

return_split cover_node_051 edge_at .oldSmall box((45/128:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_047 right_from cover_node_050

return_split cover_node_052 edge_at .oldSmall box((11/32:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (45/128:ℝ) left_from cover_node_045 right_from cover_node_051

return_split cover_node_053 edge_at .oldSmall box((21/64:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (11/32:ℝ) left_from cover_node_039 right_from cover_node_052

return_split cover_node_054 edge_at .oldSmall box((0:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (21/64:ℝ) left_from cover_node_026 right_from cover_node_053

return_split cover_node_055 edge_at .oldSmall box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row057 right_from envelope_row058

return_split cover_node_056 edge_at .oldSmall box((23/64:ℝ),(47/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row056 right_from cover_node_055

return_split cover_node_057 edge_at .oldSmall box((23/64:ℝ),(47/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row059 right_from envelope_row060

return_split cover_node_058 edge_at .oldSmall box((23/64:ℝ),(47/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row061 right_from envelope_row062

return_split cover_node_059 edge_at .oldSmall box((23/64:ℝ),(47/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_057 right_from cover_node_058

return_split cover_node_060 edge_at .oldSmall box((23/64:ℝ),(47/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_056 right_from cover_node_059

return_split cover_node_061 edge_at .oldSmall box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row064 right_from envelope_row065

return_split cover_node_062 edge_at .oldSmall box((47/128:ℝ),(3/8:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row063 right_from cover_node_061

return_split cover_node_063 edge_at .oldSmall box((47/128:ℝ),(3/8:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row066 right_from envelope_row067

return_split cover_node_064 edge_at .oldSmall box((47/128:ℝ),(3/8:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row068 right_from envelope_row069

return_split cover_node_065 edge_at .oldSmall box((47/128:ℝ),(3/8:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_063 right_from cover_node_064

return_split cover_node_066 edge_at .oldSmall box((47/128:ℝ),(3/8:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_062 right_from cover_node_065

return_split cover_node_067 edge_at .oldSmall box((23/64:ℝ),(3/8:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (47/128:ℝ) left_from cover_node_060 right_from cover_node_066

return_split cover_node_068 edge_at .oldSmall box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row071 right_from envelope_row072

return_split cover_node_069 edge_at .oldSmall box((3/8:ℝ),(49/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row070 right_from cover_node_068

return_split cover_node_070 edge_at .oldSmall box((3/8:ℝ),(49/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row073 right_from envelope_row074

return_split cover_node_071 edge_at .oldSmall box((3/8:ℝ),(49/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row075 right_from envelope_row076

return_split cover_node_072 edge_at .oldSmall box((3/8:ℝ),(49/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_070 right_from cover_node_071

return_split cover_node_073 edge_at .oldSmall box((3/8:ℝ),(49/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_069 right_from cover_node_072

return_split cover_node_074 edge_at .oldSmall box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row078 right_from envelope_row079

return_split cover_node_075 edge_at .oldSmall box((49/128:ℝ),(25/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row077 right_from cover_node_074

return_split cover_node_076 edge_at .oldSmall box((49/128:ℝ),(25/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row080 right_from envelope_row081

return_split cover_node_077 edge_at .oldSmall box((49/128:ℝ),(25/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row082 right_from envelope_row083

return_split cover_node_078 edge_at .oldSmall box((49/128:ℝ),(25/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_076 right_from cover_node_077

return_split cover_node_079 edge_at .oldSmall box((49/128:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_075 right_from cover_node_078

return_split cover_node_080 edge_at .oldSmall box((3/8:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (49/128:ℝ) left_from cover_node_073 right_from cover_node_079

return_split cover_node_081 edge_at .oldSmall box((23/64:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (3/8:ℝ) left_from cover_node_067 right_from cover_node_080

return_split cover_node_082 edge_at .oldSmall box((25/64:ℝ),(401/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row085 right_from envelope_row086

return_split cover_node_083 edge_at .oldSmall box((25/64:ℝ),(401/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row084 right_from cover_node_082

return_split cover_node_084 edge_at .oldSmall box((25/64:ℝ),(401/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row087 right_from envelope_row088

return_split cover_node_085 edge_at .oldSmall box((25/64:ℝ),(401/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row089 right_from envelope_row090

return_split cover_node_086 edge_at .oldSmall box((25/64:ℝ),(401/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_084 right_from cover_node_085

return_split cover_node_087 edge_at .oldSmall box((25/64:ℝ),(401/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_083 right_from cover_node_086

return_split cover_node_088 edge_at .oldSmall box((401/1024:ℝ),(201/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row092 right_from envelope_row093

return_split cover_node_089 edge_at .oldSmall box((401/1024:ℝ),(201/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row091 right_from cover_node_088

return_split cover_node_090 edge_at .oldSmall box((401/1024:ℝ),(201/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row094 right_from envelope_row095

return_split cover_node_091 edge_at .oldSmall box((401/1024:ℝ),(201/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row096 right_from envelope_row097

return_split cover_node_092 edge_at .oldSmall box((401/1024:ℝ),(201/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_090 right_from cover_node_091

return_split cover_node_093 edge_at .oldSmall box((401/1024:ℝ),(201/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_089 right_from cover_node_092

return_split cover_node_094 edge_at .oldSmall box((25/64:ℝ),(201/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (401/1024:ℝ) left_from cover_node_087 right_from cover_node_093

return_split cover_node_095 edge_at .oldSmall box((201/512:ℝ),(403/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row099 right_from envelope_row100

return_split cover_node_096 edge_at .oldSmall box((201/512:ℝ),(403/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row098 right_from cover_node_095

return_split cover_node_097 edge_at .oldSmall box((201/512:ℝ),(403/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row101 right_from envelope_row102

return_split cover_node_098 edge_at .oldSmall box((201/512:ℝ),(403/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row103 right_from envelope_row104

return_split cover_node_099 edge_at .oldSmall box((201/512:ℝ),(403/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_097 right_from cover_node_098

return_split cover_node_100 edge_at .oldSmall box((201/512:ℝ),(403/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_096 right_from cover_node_099

return_split cover_node_101 edge_at .oldSmall box((403/1024:ℝ),(101/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row106 right_from envelope_row107

return_split cover_node_102 edge_at .oldSmall box((403/1024:ℝ),(101/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row105 right_from cover_node_101

return_split cover_node_103 edge_at .oldSmall box((403/1024:ℝ),(101/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row108 right_from envelope_row109

return_split cover_node_104 edge_at .oldSmall box((403/1024:ℝ),(101/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row110 right_from envelope_row111

return_split cover_node_105 edge_at .oldSmall box((403/1024:ℝ),(101/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_103 right_from cover_node_104

return_split cover_node_106 edge_at .oldSmall box((403/1024:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_102 right_from cover_node_105

return_split cover_node_107 edge_at .oldSmall box((201/512:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (403/1024:ℝ) left_from cover_node_100 right_from cover_node_106

return_split cover_node_108 edge_at .oldSmall box((25/64:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (201/512:ℝ) left_from cover_node_094 right_from cover_node_107

return_split cover_node_109 edge_at .oldSmall box((23/64:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (25/64:ℝ) left_from cover_node_081 right_from cover_node_108

return_split cover_node_110 edge_at .oldSmall box((0:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (23/64:ℝ) left_from cover_node_054 right_from cover_node_109

return_split cover_node_111 edge_at .oldSmall box((101/256:ℝ),(405/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row113 right_from envelope_row114

return_split cover_node_112 edge_at .oldSmall box((101/256:ℝ),(405/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row112 right_from cover_node_111

return_split cover_node_113 edge_at .oldSmall box((101/256:ℝ),(405/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row115 right_from envelope_row116

return_split cover_node_114 edge_at .oldSmall box((101/256:ℝ),(405/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row117 right_from envelope_row118

return_split cover_node_115 edge_at .oldSmall box((101/256:ℝ),(405/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_113 right_from cover_node_114

return_split cover_node_116 edge_at .oldSmall box((101/256:ℝ),(405/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_112 right_from cover_node_115

return_split cover_node_117 edge_at .oldSmall box((405/1024:ℝ),(203/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row120 right_from envelope_row121

return_split cover_node_118 edge_at .oldSmall box((405/1024:ℝ),(203/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row119 right_from cover_node_117

return_split cover_node_119 edge_at .oldSmall box((405/1024:ℝ),(203/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row122 right_from envelope_row123

return_split cover_node_120 edge_at .oldSmall box((405/1024:ℝ),(203/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row124 right_from envelope_row125

return_split cover_node_121 edge_at .oldSmall box((405/1024:ℝ),(203/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_119 right_from cover_node_120

return_split cover_node_122 edge_at .oldSmall box((405/1024:ℝ),(203/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_118 right_from cover_node_121

return_split cover_node_123 edge_at .oldSmall box((101/256:ℝ),(203/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (405/1024:ℝ) left_from cover_node_116 right_from cover_node_122

return_split cover_node_124 edge_at .oldSmall box((203/512:ℝ),(407/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row127 right_from envelope_row128

return_split cover_node_125 edge_at .oldSmall box((203/512:ℝ),(407/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row126 right_from cover_node_124

return_split cover_node_126 edge_at .oldSmall box((203/512:ℝ),(407/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row129 right_from envelope_row130

return_split cover_node_127 edge_at .oldSmall box((203/512:ℝ),(407/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row131 right_from envelope_row132

return_split cover_node_128 edge_at .oldSmall box((203/512:ℝ),(407/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_126 right_from cover_node_127

return_split cover_node_129 edge_at .oldSmall box((203/512:ℝ),(407/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_125 right_from cover_node_128

return_split cover_node_130 edge_at .oldSmall box((407/1024:ℝ),(51/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row134 right_from envelope_row135

return_split cover_node_131 edge_at .oldSmall box((407/1024:ℝ),(51/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row133 right_from cover_node_130

return_split cover_node_132 edge_at .oldSmall box((407/1024:ℝ),(51/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row136 right_from envelope_row137

return_split cover_node_133 edge_at .oldSmall box((407/1024:ℝ),(51/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row138 right_from envelope_row139

return_split cover_node_134 edge_at .oldSmall box((407/1024:ℝ),(51/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_132 right_from cover_node_133

return_split cover_node_135 edge_at .oldSmall box((407/1024:ℝ),(51/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_131 right_from cover_node_134

return_split cover_node_136 edge_at .oldSmall box((203/512:ℝ),(51/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (407/1024:ℝ) left_from cover_node_129 right_from cover_node_135

return_split cover_node_137 edge_at .oldSmall box((101/256:ℝ),(51/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (203/512:ℝ) left_from cover_node_123 right_from cover_node_136

return_split cover_node_138 edge_at .oldSmall box((51/128:ℝ),(13/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row141 right_from envelope_row142

return_split cover_node_139 edge_at .oldSmall box((51/128:ℝ),(13/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row140 right_from cover_node_138

return_split cover_node_140 edge_at .oldSmall box((51/128:ℝ),(13/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row143 right_from envelope_row144

return_split cover_node_141 edge_at .oldSmall box((51/128:ℝ),(13/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row145 right_from envelope_row146

return_split cover_node_142 edge_at .oldSmall box((51/128:ℝ),(13/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_140 right_from cover_node_141

return_split cover_node_143 edge_at .oldSmall box((51/128:ℝ),(13/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_139 right_from cover_node_142

return_split cover_node_144 edge_at .oldSmall box((13/32:ℝ),(417/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row148 right_from envelope_row149

return_split cover_node_145 edge_at .oldSmall box((13/32:ℝ),(417/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row147 right_from cover_node_144

return_split cover_node_146 edge_at .oldSmall box((13/32:ℝ),(417/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row150 right_from envelope_row151

return_split cover_node_147 edge_at .oldSmall box((13/32:ℝ),(417/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row152 right_from envelope_row153

return_split cover_node_148 edge_at .oldSmall box((13/32:ℝ),(417/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_146 right_from cover_node_147

return_split cover_node_149 edge_at .oldSmall box((13/32:ℝ),(417/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_145 right_from cover_node_148

return_split cover_node_150 edge_at .oldSmall box((51/128:ℝ),(417/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (13/32:ℝ) left_from cover_node_143 right_from cover_node_149

return_split cover_node_151 edge_at .oldSmall box((417/1024:ℝ),(209/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row155 right_from envelope_row156

return_split cover_node_152 edge_at .oldSmall box((417/1024:ℝ),(209/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row154 right_from cover_node_151

return_split cover_node_153 edge_at .oldSmall box((417/1024:ℝ),(209/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row157 right_from envelope_row158

return_split cover_node_154 edge_at .oldSmall box((417/1024:ℝ),(209/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row159 right_from envelope_row160

return_split cover_node_155 edge_at .oldSmall box((417/1024:ℝ),(209/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_153 right_from cover_node_154

return_split cover_node_156 edge_at .oldSmall box((417/1024:ℝ),(209/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_152 right_from cover_node_155

return_split cover_node_157 edge_at .oldSmall box((209/512:ℝ),(419/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row162 right_from envelope_row163

return_split cover_node_158 edge_at .oldSmall box((209/512:ℝ),(419/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row161 right_from cover_node_157

return_split cover_node_159 edge_at .oldSmall box((209/512:ℝ),(419/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row164 right_from envelope_row165

return_split cover_node_160 edge_at .oldSmall box((209/512:ℝ),(419/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row166 right_from envelope_row167

return_split cover_node_161 edge_at .oldSmall box((209/512:ℝ),(419/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_159 right_from cover_node_160

return_split cover_node_162 edge_at .oldSmall box((209/512:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_158 right_from cover_node_161

return_split cover_node_163 edge_at .oldSmall box((417/1024:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (209/512:ℝ) left_from cover_node_156 right_from cover_node_162

return_split cover_node_164 edge_at .oldSmall box((51/128:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (417/1024:ℝ) left_from cover_node_150 right_from cover_node_163

return_split cover_node_165 edge_at .oldSmall box((101/256:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (51/128:ℝ) left_from cover_node_137 right_from cover_node_164

return_split cover_node_166 edge_at .oldSmall box((419/1024:ℝ),(105/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row169 right_from envelope_row170

return_split cover_node_167 edge_at .oldSmall box((419/1024:ℝ),(105/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row168 right_from cover_node_166

return_split cover_node_168 edge_at .oldSmall box((419/1024:ℝ),(105/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row171 right_from envelope_row172

return_split cover_node_169 edge_at .oldSmall box((419/1024:ℝ),(105/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row173 right_from envelope_row174

return_split cover_node_170 edge_at .oldSmall box((419/1024:ℝ),(105/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_168 right_from cover_node_169

return_split cover_node_171 edge_at .oldSmall box((419/1024:ℝ),(105/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_167 right_from cover_node_170

return_split cover_node_172 edge_at .oldSmall box((105/256:ℝ),(421/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row176 right_from envelope_row177

return_split cover_node_173 edge_at .oldSmall box((105/256:ℝ),(421/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row175 right_from cover_node_172

return_split cover_node_174 edge_at .oldSmall box((105/256:ℝ),(421/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row178 right_from envelope_row179

return_split cover_node_175 edge_at .oldSmall box((105/256:ℝ),(421/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row180 right_from envelope_row181

return_split cover_node_176 edge_at .oldSmall box((105/256:ℝ),(421/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_174 right_from cover_node_175

return_split cover_node_177 edge_at .oldSmall box((105/256:ℝ),(421/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_173 right_from cover_node_176

return_split cover_node_178 edge_at .oldSmall box((419/1024:ℝ),(421/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (105/256:ℝ) left_from cover_node_171 right_from cover_node_177

return_split cover_node_179 edge_at .oldSmall box((421/1024:ℝ),(211/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row183 right_from envelope_row184

return_split cover_node_180 edge_at .oldSmall box((421/1024:ℝ),(211/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row182 right_from cover_node_179

return_split cover_node_181 edge_at .oldSmall box((421/1024:ℝ),(211/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row185 right_from envelope_row186

return_split cover_node_182 edge_at .oldSmall box((421/1024:ℝ),(211/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row187 right_from envelope_row188

return_split cover_node_183 edge_at .oldSmall box((421/1024:ℝ),(211/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_181 right_from cover_node_182

return_split cover_node_184 edge_at .oldSmall box((421/1024:ℝ),(211/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_180 right_from cover_node_183

return_split cover_node_185 edge_at .oldSmall box((211/512:ℝ),(423/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row190 right_from envelope_row191

return_split cover_node_186 edge_at .oldSmall box((211/512:ℝ),(423/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row189 right_from cover_node_185

return_split cover_node_187 edge_at .oldSmall box((211/512:ℝ),(423/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row192 right_from envelope_row193

return_split cover_node_188 edge_at .oldSmall box((211/512:ℝ),(423/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row194 right_from envelope_row195

return_split cover_node_189 edge_at .oldSmall box((211/512:ℝ),(423/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_187 right_from cover_node_188

return_split cover_node_190 edge_at .oldSmall box((211/512:ℝ),(423/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_186 right_from cover_node_189

return_split cover_node_191 edge_at .oldSmall box((421/1024:ℝ),(423/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (211/512:ℝ) left_from cover_node_184 right_from cover_node_190

return_split cover_node_192 edge_at .oldSmall box((419/1024:ℝ),(423/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (421/1024:ℝ) left_from cover_node_178 right_from cover_node_191

return_split cover_node_193 edge_at .oldSmall box((423/1024:ℝ),(53/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row197 right_from envelope_row198

return_split cover_node_194 edge_at .oldSmall box((423/1024:ℝ),(53/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row196 right_from cover_node_193

return_split cover_node_195 edge_at .oldSmall box((423/1024:ℝ),(53/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row199 right_from envelope_row200

return_split cover_node_196 edge_at .oldSmall box((423/1024:ℝ),(53/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row201 right_from envelope_row202

return_split cover_node_197 edge_at .oldSmall box((423/1024:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_195 right_from cover_node_196

return_split cover_node_198 edge_at .oldSmall box((423/1024:ℝ),(53/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_194 right_from cover_node_197

return_split cover_node_199 edge_at .oldSmall box((53/128:ℝ),(425/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row204 right_from envelope_row205

return_split cover_node_200 edge_at .oldSmall box((53/128:ℝ),(425/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row203 right_from cover_node_199

return_split cover_node_201 edge_at .oldSmall box((53/128:ℝ),(425/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row206 right_from envelope_row207

return_split cover_node_202 edge_at .oldSmall box((53/128:ℝ),(425/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row208 right_from envelope_row209

return_split cover_node_203 edge_at .oldSmall box((53/128:ℝ),(425/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_201 right_from cover_node_202

return_split cover_node_204 edge_at .oldSmall box((53/128:ℝ),(425/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_200 right_from cover_node_203

return_split cover_node_205 edge_at .oldSmall box((423/1024:ℝ),(425/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (53/128:ℝ) left_from cover_node_198 right_from cover_node_204

return_split cover_node_206 edge_at .oldSmall box((425/1024:ℝ),(213/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row211 right_from envelope_row212

return_split cover_node_207 edge_at .oldSmall box((425/1024:ℝ),(213/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row210 right_from cover_node_206

return_split cover_node_208 edge_at .oldSmall box((425/1024:ℝ),(213/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row213 right_from envelope_row214

return_split cover_node_209 edge_at .oldSmall box((425/1024:ℝ),(213/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row215 right_from envelope_row216

return_split cover_node_210 edge_at .oldSmall box((425/1024:ℝ),(213/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_208 right_from cover_node_209

return_split cover_node_211 edge_at .oldSmall box((425/1024:ℝ),(213/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_207 right_from cover_node_210

return_split cover_node_212 edge_at .oldSmall box((213/512:ℝ),(427/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row218 right_from envelope_row219

return_split cover_node_213 edge_at .oldSmall box((213/512:ℝ),(427/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row217 right_from cover_node_212

return_split cover_node_214 edge_at .oldSmall box((213/512:ℝ),(427/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row220 right_from envelope_row221

return_split cover_node_215 edge_at .oldSmall box((213/512:ℝ),(427/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row222 right_from envelope_row223

return_split cover_node_216 edge_at .oldSmall box((213/512:ℝ),(427/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_214 right_from cover_node_215

return_split cover_node_217 edge_at .oldSmall box((213/512:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_213 right_from cover_node_216

return_split cover_node_218 edge_at .oldSmall box((425/1024:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (213/512:ℝ) left_from cover_node_211 right_from cover_node_217

return_split cover_node_219 edge_at .oldSmall box((423/1024:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (425/1024:ℝ) left_from cover_node_205 right_from cover_node_218

return_split cover_node_220 edge_at .oldSmall box((419/1024:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (423/1024:ℝ) left_from cover_node_192 right_from cover_node_219

return_split cover_node_221 edge_at .oldSmall box((101/256:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (419/1024:ℝ) left_from cover_node_165 right_from cover_node_220

return_split cover_node_222 edge_at .oldSmall box((0:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (101/256:ℝ) left_from cover_node_110 right_from cover_node_221

return_split cover_node_223 edge_at .oldSmall box((427/1024:ℝ),(107/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row225 right_from envelope_row226

return_split cover_node_224 edge_at .oldSmall box((427/1024:ℝ),(107/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row224 right_from cover_node_223

return_split cover_node_225 edge_at .oldSmall box((427/1024:ℝ),(107/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row227 right_from envelope_row228

return_split cover_node_226 edge_at .oldSmall box((427/1024:ℝ),(107/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row229 right_from envelope_row230

return_split cover_node_227 edge_at .oldSmall box((427/1024:ℝ),(107/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_225 right_from cover_node_226

return_split cover_node_228 edge_at .oldSmall box((427/1024:ℝ),(107/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_224 right_from cover_node_227

return_split cover_node_229 edge_at .oldSmall box((107/256:ℝ),(429/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row232 right_from envelope_row233

return_split cover_node_230 edge_at .oldSmall box((107/256:ℝ),(429/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row231 right_from cover_node_229

return_split cover_node_231 edge_at .oldSmall box((107/256:ℝ),(429/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row234 right_from envelope_row235

return_split cover_node_232 edge_at .oldSmall box((107/256:ℝ),(429/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row236 right_from envelope_row237

return_split cover_node_233 edge_at .oldSmall box((107/256:ℝ),(429/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_231 right_from cover_node_232

return_split cover_node_234 edge_at .oldSmall box((107/256:ℝ),(429/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_230 right_from cover_node_233

return_split cover_node_235 edge_at .oldSmall box((427/1024:ℝ),(429/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (107/256:ℝ) left_from cover_node_228 right_from cover_node_234

return_split cover_node_236 edge_at .oldSmall box((429/1024:ℝ),(215/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row239 right_from envelope_row240

return_split cover_node_237 edge_at .oldSmall box((429/1024:ℝ),(215/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row238 right_from cover_node_236

return_split cover_node_238 edge_at .oldSmall box((429/1024:ℝ),(215/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row241 right_from envelope_row242

return_split cover_node_239 edge_at .oldSmall box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row243 right_from envelope_row244

return_split cover_node_240 edge_at .oldSmall box((429/1024:ℝ),(215/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_238 right_from cover_node_239

return_split cover_node_241 edge_at .oldSmall box((429/1024:ℝ),(215/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_237 right_from cover_node_240

return_split cover_node_242 edge_at .oldSmall box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row246 right_from envelope_row247

return_split cover_node_243 edge_at .oldSmall box((215/512:ℝ),(431/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row245 right_from cover_node_242

return_split cover_node_244 edge_at .oldSmall box((215/512:ℝ),(431/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row248 right_from envelope_row249

return_split cover_node_245 edge_at .oldSmall box((215/512:ℝ),(431/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row250 right_from envelope_row251

return_split cover_node_246 edge_at .oldSmall box((215/512:ℝ),(431/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_244 right_from cover_node_245

return_split cover_node_247 edge_at .oldSmall box((215/512:ℝ),(431/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_243 right_from cover_node_246

return_split cover_node_248 edge_at .oldSmall box((429/1024:ℝ),(431/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (215/512:ℝ) left_from cover_node_241 right_from cover_node_247

return_split cover_node_249 edge_at .oldSmall box((427/1024:ℝ),(431/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (429/1024:ℝ) left_from cover_node_235 right_from cover_node_248

return_split cover_node_250 edge_at .oldSmall box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row253 right_from envelope_row254

return_split cover_node_251 edge_at .oldSmall box((431/1024:ℝ),(27/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row252 right_from cover_node_250

return_split cover_node_252 edge_at .oldSmall box((431/1024:ℝ),(27/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row255 right_from envelope_row256

return_split cover_node_253 edge_at .oldSmall box((431/1024:ℝ),(27/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row257 right_from envelope_row258

return_split cover_node_254 edge_at .oldSmall box((431/1024:ℝ),(27/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_252 right_from cover_node_253

return_split cover_node_255 edge_at .oldSmall box((431/1024:ℝ),(27/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_251 right_from cover_node_254

return_split cover_node_256 edge_at .oldSmall box((27/64:ℝ),(433/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row260 right_from envelope_row261

return_split cover_node_257 edge_at .oldSmall box((27/64:ℝ),(433/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row259 right_from cover_node_256

return_split cover_node_258 edge_at .oldSmall box((27/64:ℝ),(433/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row262 right_from envelope_row263

return_split cover_node_259 edge_at .oldSmall box((27/64:ℝ),(433/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row264 right_from envelope_row265

return_split cover_node_260 edge_at .oldSmall box((27/64:ℝ),(433/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_258 right_from cover_node_259

return_split cover_node_261 edge_at .oldSmall box((27/64:ℝ),(433/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_257 right_from cover_node_260

return_split cover_node_262 edge_at .oldSmall box((431/1024:ℝ),(433/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (27/64:ℝ) left_from cover_node_255 right_from cover_node_261

return_split cover_node_263 edge_at .oldSmall box((433/1024:ℝ),(217/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row267 right_from envelope_row268

return_split cover_node_264 edge_at .oldSmall box((433/1024:ℝ),(217/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row266 right_from cover_node_263

return_split cover_node_265 edge_at .oldSmall box((433/1024:ℝ),(217/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row269 right_from envelope_row270

return_split cover_node_266 edge_at .oldSmall box((433/1024:ℝ),(217/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row271 right_from envelope_row272

return_split cover_node_267 edge_at .oldSmall box((433/1024:ℝ),(217/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_265 right_from cover_node_266

return_split cover_node_268 edge_at .oldSmall box((433/1024:ℝ),(217/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_264 right_from cover_node_267

return_split cover_node_269 edge_at .oldSmall box((217/512:ℝ),(435/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row274 right_from envelope_row275

return_split cover_node_270 edge_at .oldSmall box((217/512:ℝ),(435/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row273 right_from cover_node_269

return_split cover_node_271 edge_at .oldSmall box((217/512:ℝ),(435/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row276 right_from envelope_row277

return_split cover_node_272 edge_at .oldSmall box((217/512:ℝ),(435/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row278 right_from envelope_row279

return_split cover_node_273 edge_at .oldSmall box((217/512:ℝ),(435/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_271 right_from cover_node_272

return_split cover_node_274 edge_at .oldSmall box((217/512:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_270 right_from cover_node_273

return_split cover_node_275 edge_at .oldSmall box((433/1024:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (217/512:ℝ) left_from cover_node_268 right_from cover_node_274

return_split cover_node_276 edge_at .oldSmall box((431/1024:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (433/1024:ℝ) left_from cover_node_262 right_from cover_node_275

return_split cover_node_277 edge_at .oldSmall box((427/1024:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (431/1024:ℝ) left_from cover_node_249 right_from cover_node_276

return_split cover_node_278 edge_at .oldSmall box((435/1024:ℝ),(109/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row281 right_from envelope_row282

return_split cover_node_279 edge_at .oldSmall box((435/1024:ℝ),(109/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row280 right_from cover_node_278

return_split cover_node_280 edge_at .oldSmall box((435/1024:ℝ),(109/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row283 right_from envelope_row284

return_split cover_node_281 edge_at .oldSmall box((435/1024:ℝ),(109/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row285 right_from envelope_row286

return_split cover_node_282 edge_at .oldSmall box((435/1024:ℝ),(109/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_280 right_from cover_node_281

return_split cover_node_283 edge_at .oldSmall box((435/1024:ℝ),(109/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_279 right_from cover_node_282

return_split cover_node_284 edge_at .oldSmall box((109/256:ℝ),(437/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row288 right_from envelope_row289

return_split cover_node_285 edge_at .oldSmall box((109/256:ℝ),(437/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row287 right_from cover_node_284

return_split cover_node_286 edge_at .oldSmall box((109/256:ℝ),(437/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row290 right_from envelope_row291

return_split cover_node_287 edge_at .oldSmall box((109/256:ℝ),(437/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row292 right_from envelope_row293

return_split cover_node_288 edge_at .oldSmall box((109/256:ℝ),(437/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_286 right_from cover_node_287

return_split cover_node_289 edge_at .oldSmall box((109/256:ℝ),(437/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_285 right_from cover_node_288

return_split cover_node_290 edge_at .oldSmall box((435/1024:ℝ),(437/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (109/256:ℝ) left_from cover_node_283 right_from cover_node_289

return_split cover_node_291 edge_at .oldSmall box((437/1024:ℝ),(219/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row295 right_from envelope_row296

return_split cover_node_292 edge_at .oldSmall box((437/1024:ℝ),(219/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row294 right_from cover_node_291

return_split cover_node_293 edge_at .oldSmall box((437/1024:ℝ),(219/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row297 right_from envelope_row298

return_split cover_node_294 edge_at .oldSmall box((437/1024:ℝ),(219/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row299 right_from envelope_row300

return_split cover_node_295 edge_at .oldSmall box((437/1024:ℝ),(219/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_293 right_from cover_node_294

return_split cover_node_296 edge_at .oldSmall box((437/1024:ℝ),(219/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_292 right_from cover_node_295

return_split cover_node_297 edge_at .oldSmall box((219/512:ℝ),(439/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row302 right_from envelope_row303

return_split cover_node_298 edge_at .oldSmall box((219/512:ℝ),(439/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row301 right_from cover_node_297

return_split cover_node_299 edge_at .oldSmall box((219/512:ℝ),(439/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row304 right_from envelope_row305

return_split cover_node_300 edge_at .oldSmall box((219/512:ℝ),(439/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row306 right_from envelope_row307

return_split cover_node_301 edge_at .oldSmall box((219/512:ℝ),(439/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_299 right_from cover_node_300

return_split cover_node_302 edge_at .oldSmall box((219/512:ℝ),(439/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_298 right_from cover_node_301

return_split cover_node_303 edge_at .oldSmall box((437/1024:ℝ),(439/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (219/512:ℝ) left_from cover_node_296 right_from cover_node_302

return_split cover_node_304 edge_at .oldSmall box((435/1024:ℝ),(439/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (437/1024:ℝ) left_from cover_node_290 right_from cover_node_303

return_split cover_node_305 edge_at .oldSmall box((439/1024:ℝ),(55/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row309 right_from envelope_row310

return_split cover_node_306 edge_at .oldSmall box((439/1024:ℝ),(55/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row308 right_from cover_node_305

return_split cover_node_307 edge_at .oldSmall box((439/1024:ℝ),(55/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row311 right_from envelope_row312

return_split cover_node_308 edge_at .oldSmall box((439/1024:ℝ),(55/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row313 right_from envelope_row314

return_split cover_node_309 edge_at .oldSmall box((439/1024:ℝ),(55/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_307 right_from cover_node_308

return_split cover_node_310 edge_at .oldSmall box((439/1024:ℝ),(55/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_306 right_from cover_node_309

return_split cover_node_311 edge_at .oldSmall box((55/128:ℝ),(111/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row316 right_from envelope_row317

return_split cover_node_312 edge_at .oldSmall box((55/128:ℝ),(111/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row315 right_from cover_node_311

return_split cover_node_313 edge_at .oldSmall box((55/128:ℝ),(111/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row318 right_from envelope_row319

return_split cover_node_314 edge_at .oldSmall box((55/128:ℝ),(111/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row320 right_from envelope_row321

return_split cover_node_315 edge_at .oldSmall box((55/128:ℝ),(111/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_313 right_from cover_node_314

return_split cover_node_316 edge_at .oldSmall box((55/128:ℝ),(111/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_312 right_from cover_node_315

return_split cover_node_317 edge_at .oldSmall box((439/1024:ℝ),(111/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (55/128:ℝ) left_from cover_node_310 right_from cover_node_316

return_split cover_node_318 edge_at .oldSmall box((111/256:ℝ),(7/16:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row323 right_from envelope_row324

return_split cover_node_319 edge_at .oldSmall box((111/256:ℝ),(7/16:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row322 right_from cover_node_318

return_split cover_node_320 edge_at .oldSmall box((111/256:ℝ),(7/16:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row325 right_from envelope_row326

return_split cover_node_321 edge_at .oldSmall box((111/256:ℝ),(7/16:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row327 right_from envelope_row328

return_split cover_node_322 edge_at .oldSmall box((111/256:ℝ),(7/16:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_320 right_from cover_node_321

return_split cover_node_323 edge_at .oldSmall box((111/256:ℝ),(7/16:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_319 right_from cover_node_322

return_split cover_node_324 edge_at .oldSmall box((7/16:ℝ),(225/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row330 right_from envelope_row331

return_split cover_node_325 edge_at .oldSmall box((7/16:ℝ),(225/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row329 right_from cover_node_324

return_split cover_node_326 edge_at .oldSmall box((7/16:ℝ),(225/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row332 right_from envelope_row333

return_split cover_node_327 edge_at .oldSmall box((7/16:ℝ),(225/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row334 right_from envelope_row335

return_split cover_node_328 edge_at .oldSmall box((7/16:ℝ),(225/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_326 right_from cover_node_327

return_split cover_node_329 edge_at .oldSmall box((7/16:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_325 right_from cover_node_328

return_split cover_node_330 edge_at .oldSmall box((111/256:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (7/16:ℝ) left_from cover_node_323 right_from cover_node_329

return_split cover_node_331 edge_at .oldSmall box((439/1024:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (111/256:ℝ) left_from cover_node_317 right_from cover_node_330

return_split cover_node_332 edge_at .oldSmall box((435/1024:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (439/1024:ℝ) left_from cover_node_304 right_from cover_node_331

return_split cover_node_333 edge_at .oldSmall box((427/1024:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (435/1024:ℝ) left_from cover_node_277 right_from cover_node_332

return_split cover_node_334 edge_at .oldSmall box((225/512:ℝ),(453/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row337 right_from envelope_row338

return_split cover_node_335 edge_at .oldSmall box((225/512:ℝ),(453/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row336 right_from cover_node_334

return_split cover_node_336 edge_at .oldSmall box((225/512:ℝ),(453/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row339 right_from envelope_row340

return_split cover_node_337 edge_at .oldSmall box((225/512:ℝ),(453/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row341 right_from envelope_row342

return_split cover_node_338 edge_at .oldSmall box((225/512:ℝ),(453/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_336 right_from cover_node_337

return_split cover_node_339 edge_at .oldSmall box((225/512:ℝ),(453/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_335 right_from cover_node_338

return_split cover_node_340 edge_at .oldSmall box((453/1024:ℝ),(57/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row344 right_from envelope_row345

return_split cover_node_341 edge_at .oldSmall box((453/1024:ℝ),(57/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row343 right_from cover_node_340

return_split cover_node_342 edge_at .oldSmall box((453/1024:ℝ),(57/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row346 right_from envelope_row347

return_split cover_node_343 edge_at .oldSmall box((453/1024:ℝ),(57/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row348 right_from envelope_row349

return_split cover_node_344 edge_at .oldSmall box((453/1024:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_342 right_from cover_node_343

return_split cover_node_345 edge_at .oldSmall box((453/1024:ℝ),(57/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_341 right_from cover_node_344

return_split cover_node_346 edge_at .oldSmall box((225/512:ℝ),(57/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (453/1024:ℝ) left_from cover_node_339 right_from cover_node_345

return_split cover_node_347 edge_at .oldSmall box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row351 right_from envelope_row352

return_split cover_node_348 edge_at .oldSmall box((57/128:ℝ),(29/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row350 right_from cover_node_347

return_split cover_node_349 edge_at .oldSmall box((57/128:ℝ),(29/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row353 right_from envelope_row354

return_split cover_node_350 edge_at .oldSmall box((57/128:ℝ),(29/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row355 right_from envelope_row356

return_split cover_node_351 edge_at .oldSmall box((57/128:ℝ),(29/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_349 right_from cover_node_350

return_split cover_node_352 edge_at .oldSmall box((57/128:ℝ),(29/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_348 right_from cover_node_351

return_split cover_node_353 edge_at .oldSmall box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row358 right_from envelope_row359

return_split cover_node_354 edge_at .oldSmall box((29/64:ℝ),(59/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row357 right_from cover_node_353

return_split cover_node_355 edge_at .oldSmall box((29/64:ℝ),(59/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row360 right_from envelope_row361

return_split cover_node_356 edge_at .oldSmall box((29/64:ℝ),(59/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row362 right_from envelope_row363

return_split cover_node_357 edge_at .oldSmall box((29/64:ℝ),(59/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_355 right_from cover_node_356

return_split cover_node_358 edge_at .oldSmall box((29/64:ℝ),(59/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_354 right_from cover_node_357

return_split cover_node_359 edge_at .oldSmall box((57/128:ℝ),(59/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (29/64:ℝ) left_from cover_node_352 right_from cover_node_358

return_split cover_node_360 edge_at .oldSmall box((225/512:ℝ),(59/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (57/128:ℝ) left_from cover_node_346 right_from cover_node_359

return_split cover_node_361 edge_at .oldSmall box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row365 right_from envelope_row366

return_split cover_node_362 edge_at .oldSmall box((59/128:ℝ),(15/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row364 right_from cover_node_361

return_split cover_node_363 edge_at .oldSmall box((59/128:ℝ),(15/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row367 right_from envelope_row368

return_split cover_node_364 edge_at .oldSmall box((59/128:ℝ),(15/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row369 right_from envelope_row370

return_split cover_node_365 edge_at .oldSmall box((59/128:ℝ),(15/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_363 right_from cover_node_364

return_split cover_node_366 edge_at .oldSmall box((59/128:ℝ),(15/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_362 right_from cover_node_365

return_split cover_node_367 edge_at .oldSmall box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row372 right_from envelope_row373

return_split cover_node_368 edge_at .oldSmall box((15/32:ℝ),(61/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row371 right_from cover_node_367

return_split cover_node_369 edge_at .oldSmall box((15/32:ℝ),(61/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row374 right_from envelope_row375

return_split cover_node_370 edge_at .oldSmall box((15/32:ℝ),(61/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row376 right_from envelope_row377

return_split cover_node_371 edge_at .oldSmall box((15/32:ℝ),(61/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_369 right_from cover_node_370

return_split cover_node_372 edge_at .oldSmall box((15/32:ℝ),(61/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_368 right_from cover_node_371

return_split cover_node_373 edge_at .oldSmall box((59/128:ℝ),(61/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (15/32:ℝ) left_from cover_node_366 right_from cover_node_372

return_split cover_node_374 edge_at .oldSmall box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row379 right_from envelope_row380

return_split cover_node_375 edge_at .oldSmall box((61/128:ℝ),(31/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row378 right_from cover_node_374

return_split cover_node_376 edge_at .oldSmall box((61/128:ℝ),(31/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row381 right_from envelope_row382

return_split cover_node_377 edge_at .oldSmall box((61/128:ℝ),(31/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row383 right_from envelope_row384

return_split cover_node_378 edge_at .oldSmall box((61/128:ℝ),(31/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_376 right_from cover_node_377

return_split cover_node_379 edge_at .oldSmall box((61/128:ℝ),(31/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_375 right_from cover_node_378

return_split cover_node_380 edge_at .oldSmall box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row386 right_from envelope_row387

return_split cover_node_381 edge_at .oldSmall box((31/64:ℝ),(63/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row385 right_from cover_node_380

return_split cover_node_382 edge_at .oldSmall box((31/64:ℝ),(63/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row388 right_from envelope_row389

return_split cover_node_383 edge_at .oldSmall box((31/64:ℝ),(63/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row390 right_from envelope_row391

return_split cover_node_384 edge_at .oldSmall box((31/64:ℝ),(63/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_382 right_from cover_node_383

return_split cover_node_385 edge_at .oldSmall box((31/64:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_381 right_from cover_node_384

return_split cover_node_386 edge_at .oldSmall box((61/128:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (31/64:ℝ) left_from cover_node_379 right_from cover_node_385

return_split cover_node_387 edge_at .oldSmall box((59/128:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (61/128:ℝ) left_from cover_node_373 right_from cover_node_386

return_split cover_node_388 edge_at .oldSmall box((225/512:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (59/128:ℝ) left_from cover_node_360 right_from cover_node_387

return_split cover_node_389 edge_at .oldSmall box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row393 right_from envelope_row394

return_split cover_node_390 edge_at .oldSmall box((63/128:ℝ),(1/2:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row392 right_from cover_node_389

return_split cover_node_391 edge_at .oldSmall box((63/128:ℝ),(1/2:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row395 right_from envelope_row396

return_split cover_node_392 edge_at .oldSmall box((63/128:ℝ),(1/2:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row397 right_from envelope_row398

return_split cover_node_393 edge_at .oldSmall box((63/128:ℝ),(1/2:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_391 right_from cover_node_392

return_split cover_node_394 edge_at .oldSmall box((63/128:ℝ),(1/2:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_390 right_from cover_node_393

return_split cover_node_395 edge_at .oldSmall box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row400 right_from envelope_row401

return_split cover_node_396 edge_at .oldSmall box((1/2:ℝ),(65/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row399 right_from cover_node_395

return_split cover_node_397 edge_at .oldSmall box((1/2:ℝ),(65/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row402 right_from envelope_row403

return_split cover_node_398 edge_at .oldSmall box((1/2:ℝ),(65/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row404 right_from envelope_row405

return_split cover_node_399 edge_at .oldSmall box((1/2:ℝ),(65/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_397 right_from cover_node_398

return_split cover_node_400 edge_at .oldSmall box((1/2:ℝ),(65/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_396 right_from cover_node_399

return_split cover_node_401 edge_at .oldSmall box((63/128:ℝ),(65/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (1/2:ℝ) left_from cover_node_394 right_from cover_node_400

return_split cover_node_402 edge_at .oldSmall box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row407 right_from envelope_row408

return_split cover_node_403 edge_at .oldSmall box((65/128:ℝ),(33/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row406 right_from cover_node_402

return_split cover_node_404 edge_at .oldSmall box((65/128:ℝ),(33/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row409 right_from envelope_row410

return_split cover_node_405 edge_at .oldSmall box((65/128:ℝ),(33/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row411 right_from envelope_row412

return_split cover_node_406 edge_at .oldSmall box((65/128:ℝ),(33/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_404 right_from cover_node_405

return_split cover_node_407 edge_at .oldSmall box((65/128:ℝ),(33/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_403 right_from cover_node_406

return_split cover_node_408 edge_at .oldSmall box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row414 right_from envelope_row415

return_split cover_node_409 edge_at .oldSmall box((33/64:ℝ),(67/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row413 right_from cover_node_408

return_split cover_node_410 edge_at .oldSmall box((33/64:ℝ),(67/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row416 right_from envelope_row417

return_split cover_node_411 edge_at .oldSmall box((33/64:ℝ),(67/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row418 right_from envelope_row419

return_split cover_node_412 edge_at .oldSmall box((33/64:ℝ),(67/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_410 right_from cover_node_411

return_split cover_node_413 edge_at .oldSmall box((33/64:ℝ),(67/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_409 right_from cover_node_412

return_split cover_node_414 edge_at .oldSmall box((65/128:ℝ),(67/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (33/64:ℝ) left_from cover_node_407 right_from cover_node_413

return_split cover_node_415 edge_at .oldSmall box((63/128:ℝ),(67/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (65/128:ℝ) left_from cover_node_401 right_from cover_node_414

return_split cover_node_416 edge_at .oldSmall box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row421 right_from envelope_row422

return_split cover_node_417 edge_at .oldSmall box((67/128:ℝ),(17/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row420 right_from cover_node_416

return_split cover_node_418 edge_at .oldSmall box((67/128:ℝ),(17/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row423 right_from envelope_row424

return_split cover_node_419 edge_at .oldSmall box((67/128:ℝ),(17/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row425 right_from envelope_row426

return_split cover_node_420 edge_at .oldSmall box((67/128:ℝ),(17/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_418 right_from cover_node_419

return_split cover_node_421 edge_at .oldSmall box((67/128:ℝ),(17/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_417 right_from cover_node_420

return_split cover_node_422 edge_at .oldSmall box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row428 right_from envelope_row429

return_split cover_node_423 edge_at .oldSmall box((17/32:ℝ),(69/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row427 right_from cover_node_422

return_split cover_node_424 edge_at .oldSmall box((17/32:ℝ),(69/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row430 right_from envelope_row431

return_split cover_node_425 edge_at .oldSmall box((17/32:ℝ),(69/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row432 right_from envelope_row433

return_split cover_node_426 edge_at .oldSmall box((17/32:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_424 right_from cover_node_425

return_split cover_node_427 edge_at .oldSmall box((17/32:ℝ),(69/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_423 right_from cover_node_426

return_split cover_node_428 edge_at .oldSmall box((67/128:ℝ),(69/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (17/32:ℝ) left_from cover_node_421 right_from cover_node_427

return_split cover_node_429 edge_at .oldSmall box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row435 right_from envelope_row436

return_split cover_node_430 edge_at .oldSmall box((69/128:ℝ),(35/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row434 right_from cover_node_429

return_split cover_node_431 edge_at .oldSmall box((69/128:ℝ),(35/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row437 right_from envelope_row438

return_split cover_node_432 edge_at .oldSmall box((69/128:ℝ),(35/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row439 right_from envelope_row440

return_split cover_node_433 edge_at .oldSmall box((69/128:ℝ),(35/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_431 right_from cover_node_432

return_split cover_node_434 edge_at .oldSmall box((69/128:ℝ),(35/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_430 right_from cover_node_433

return_split cover_node_435 edge_at .oldSmall box((35/64:ℝ),(3/4:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row442 right_from envelope_row443

return_split cover_node_436 edge_at .oldSmall box((35/64:ℝ),(3/4:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row441 right_from cover_node_435

return_split cover_node_437 edge_at .oldSmall box((35/64:ℝ),(3/4:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row444 right_from envelope_row445

return_split cover_node_438 edge_at .oldSmall box((35/64:ℝ),(3/4:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row446 right_from envelope_row447

return_split cover_node_439 edge_at .oldSmall box((35/64:ℝ),(3/4:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_437 right_from cover_node_438

return_split cover_node_440 edge_at .oldSmall box((35/64:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_436 right_from cover_node_439

return_split cover_node_441 edge_at .oldSmall box((69/128:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (35/64:ℝ) left_from cover_node_434 right_from cover_node_440

return_split cover_node_442 edge_at .oldSmall box((67/128:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (69/128:ℝ) left_from cover_node_428 right_from cover_node_441

return_split cover_node_443 edge_at .oldSmall box((63/128:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (67/128:ℝ) left_from cover_node_415 right_from cover_node_442

return_split cover_node_444 edge_at .oldSmall box((225/512:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (63/128:ℝ) left_from cover_node_388 right_from cover_node_443

return_split cover_node_445 edge_at .oldSmall box((427/1024:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (225/512:ℝ) left_from cover_node_333 right_from cover_node_444

return_split cover_node_446 edge_at .oldSmall box((0:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (427/1024:ℝ) left_from cover_node_222 right_from cover_node_445

return_split cover_node_447 edge_at .oldSwitch box((0:ℝ),(9/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row449 right_from envelope_row450

return_split cover_node_448 edge_at .oldSwitch box((0:ℝ),(9/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row448 right_from cover_node_447

return_split cover_node_449 edge_at .oldSwitch box((0:ℝ),(9/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row451 right_from envelope_row452

return_split cover_node_450 edge_at .oldSwitch box((0:ℝ),(9/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row453 right_from envelope_row454

return_split cover_node_451 edge_at .oldSwitch box((0:ℝ),(9/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_449 right_from cover_node_450

return_split cover_node_452 edge_at .oldSwitch box((0:ℝ),(9/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_448 right_from cover_node_451

return_split cover_node_453 edge_at .oldSwitch box((9/32:ℝ),(5/16:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row456 right_from envelope_row457

return_split cover_node_454 edge_at .oldSwitch box((9/32:ℝ),(5/16:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row455 right_from cover_node_453

return_split cover_node_455 edge_at .oldSwitch box((9/32:ℝ),(5/16:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row458 right_from envelope_row459

return_split cover_node_456 edge_at .oldSwitch box((9/32:ℝ),(5/16:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row460 right_from envelope_row461

return_split cover_node_457 edge_at .oldSwitch box((9/32:ℝ),(5/16:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_455 right_from cover_node_456

return_split cover_node_458 edge_at .oldSwitch box((9/32:ℝ),(5/16:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_454 right_from cover_node_457

return_split cover_node_459 edge_at .oldSwitch box((0:ℝ),(5/16:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (9/32:ℝ) left_from cover_node_452 right_from cover_node_458

return_split cover_node_460 edge_at .oldSwitch box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row463 right_from envelope_row464

return_split cover_node_461 edge_at .oldSwitch box((5/16:ℝ),(41/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row462 right_from cover_node_460

return_split cover_node_462 edge_at .oldSwitch box((5/16:ℝ),(41/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row465 right_from envelope_row466

return_split cover_node_463 edge_at .oldSwitch box((5/16:ℝ),(41/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row467 right_from envelope_row468

return_split cover_node_464 edge_at .oldSwitch box((5/16:ℝ),(41/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_462 right_from cover_node_463

return_split cover_node_465 edge_at .oldSwitch box((5/16:ℝ),(41/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_461 right_from cover_node_464

return_split cover_node_466 edge_at .oldSwitch box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row470 right_from envelope_row471

return_split cover_node_467 edge_at .oldSwitch box((41/128:ℝ),(21/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row469 right_from cover_node_466

return_split cover_node_468 edge_at .oldSwitch box((41/128:ℝ),(21/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row472 right_from envelope_row473

return_split cover_node_469 edge_at .oldSwitch box((41/128:ℝ),(21/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row474 right_from envelope_row475

return_split cover_node_470 edge_at .oldSwitch box((41/128:ℝ),(21/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_468 right_from cover_node_469

return_split cover_node_471 edge_at .oldSwitch box((41/128:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_467 right_from cover_node_470

return_split cover_node_472 edge_at .oldSwitch box((5/16:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (41/128:ℝ) left_from cover_node_465 right_from cover_node_471

return_split cover_node_473 edge_at .oldSwitch box((0:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (5/16:ℝ) left_from cover_node_459 right_from cover_node_472

return_split cover_node_474 edge_at .oldSwitch box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row477 right_from envelope_row478

return_split cover_node_475 edge_at .oldSwitch box((21/64:ℝ),(43/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row476 right_from cover_node_474

return_split cover_node_476 edge_at .oldSwitch box((21/64:ℝ),(43/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row479 right_from envelope_row480

return_split cover_node_477 edge_at .oldSwitch box((21/64:ℝ),(43/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row481 right_from envelope_row482

return_split cover_node_478 edge_at .oldSwitch box((21/64:ℝ),(43/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_476 right_from cover_node_477

return_split cover_node_479 edge_at .oldSwitch box((21/64:ℝ),(43/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_475 right_from cover_node_478

return_split cover_node_480 edge_at .oldSwitch box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row484 right_from envelope_row485

return_split cover_node_481 edge_at .oldSwitch box((43/128:ℝ),(11/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row483 right_from cover_node_480

return_split cover_node_482 edge_at .oldSwitch box((43/128:ℝ),(11/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row486 right_from envelope_row487

return_split cover_node_483 edge_at .oldSwitch box((43/128:ℝ),(11/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row488 right_from envelope_row489

return_split cover_node_484 edge_at .oldSwitch box((43/128:ℝ),(11/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_482 right_from cover_node_483

return_split cover_node_485 edge_at .oldSwitch box((43/128:ℝ),(11/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_481 right_from cover_node_484

return_split cover_node_486 edge_at .oldSwitch box((21/64:ℝ),(11/32:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (43/128:ℝ) left_from cover_node_479 right_from cover_node_485

return_split cover_node_487 edge_at .oldSwitch box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row491 right_from envelope_row492

return_split cover_node_488 edge_at .oldSwitch box((11/32:ℝ),(45/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row490 right_from cover_node_487

return_split cover_node_489 edge_at .oldSwitch box((11/32:ℝ),(45/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row493 right_from envelope_row494

return_split cover_node_490 edge_at .oldSwitch box((11/32:ℝ),(45/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row495 right_from envelope_row496

return_split cover_node_491 edge_at .oldSwitch box((11/32:ℝ),(45/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_489 right_from cover_node_490

return_split cover_node_492 edge_at .oldSwitch box((11/32:ℝ),(45/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_488 right_from cover_node_491

return_split cover_node_493 edge_at .oldSwitch box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row498 right_from envelope_row499

return_split cover_node_494 edge_at .oldSwitch box((45/128:ℝ),(23/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row497 right_from cover_node_493

return_split cover_node_495 edge_at .oldSwitch box((45/128:ℝ),(23/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row500 right_from envelope_row501

return_split cover_node_496 edge_at .oldSwitch box((45/128:ℝ),(23/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row502 right_from envelope_row503

return_split cover_node_497 edge_at .oldSwitch box((45/128:ℝ),(23/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_495 right_from cover_node_496

return_split cover_node_498 edge_at .oldSwitch box((45/128:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_494 right_from cover_node_497

return_split cover_node_499 edge_at .oldSwitch box((11/32:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (45/128:ℝ) left_from cover_node_492 right_from cover_node_498

return_split cover_node_500 edge_at .oldSwitch box((21/64:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (11/32:ℝ) left_from cover_node_486 right_from cover_node_499

return_split cover_node_501 edge_at .oldSwitch box((0:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (21/64:ℝ) left_from cover_node_473 right_from cover_node_500

return_split cover_node_502 edge_at .oldSwitch box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row505 right_from envelope_row506

return_split cover_node_503 edge_at .oldSwitch box((23/64:ℝ),(47/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row504 right_from cover_node_502

return_split cover_node_504 edge_at .oldSwitch box((23/64:ℝ),(47/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row507 right_from envelope_row508

return_split cover_node_505 edge_at .oldSwitch box((23/64:ℝ),(47/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row509 right_from envelope_row510

return_split cover_node_506 edge_at .oldSwitch box((23/64:ℝ),(47/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_504 right_from cover_node_505

return_split cover_node_507 edge_at .oldSwitch box((23/64:ℝ),(47/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_503 right_from cover_node_506

return_split cover_node_508 edge_at .oldSwitch box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row512 right_from envelope_row513

return_split cover_node_509 edge_at .oldSwitch box((47/128:ℝ),(3/8:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row511 right_from cover_node_508

return_split cover_node_510 edge_at .oldSwitch box((47/128:ℝ),(3/8:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row514 right_from envelope_row515

return_split cover_node_511 edge_at .oldSwitch box((47/128:ℝ),(3/8:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row516 right_from envelope_row517

return_split cover_node_512 edge_at .oldSwitch box((47/128:ℝ),(3/8:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_510 right_from cover_node_511

return_split cover_node_513 edge_at .oldSwitch box((47/128:ℝ),(3/8:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_509 right_from cover_node_512

return_split cover_node_514 edge_at .oldSwitch box((23/64:ℝ),(3/8:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (47/128:ℝ) left_from cover_node_507 right_from cover_node_513

return_split cover_node_515 edge_at .oldSwitch box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row519 right_from envelope_row520

return_split cover_node_516 edge_at .oldSwitch box((3/8:ℝ),(49/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row518 right_from cover_node_515

return_split cover_node_517 edge_at .oldSwitch box((3/8:ℝ),(49/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row521 right_from envelope_row522

return_split cover_node_518 edge_at .oldSwitch box((3/8:ℝ),(49/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row523 right_from envelope_row524

return_split cover_node_519 edge_at .oldSwitch box((3/8:ℝ),(49/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_517 right_from cover_node_518

return_split cover_node_520 edge_at .oldSwitch box((3/8:ℝ),(49/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_516 right_from cover_node_519

return_split cover_node_521 edge_at .oldSwitch box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row526 right_from envelope_row527

return_split cover_node_522 edge_at .oldSwitch box((49/128:ℝ),(25/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row525 right_from cover_node_521

return_split cover_node_523 edge_at .oldSwitch box((49/128:ℝ),(25/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row528 right_from envelope_row529

return_split cover_node_524 edge_at .oldSwitch box((49/128:ℝ),(25/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row530 right_from envelope_row531

return_split cover_node_525 edge_at .oldSwitch box((49/128:ℝ),(25/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_523 right_from cover_node_524

return_split cover_node_526 edge_at .oldSwitch box((49/128:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_522 right_from cover_node_525

return_split cover_node_527 edge_at .oldSwitch box((3/8:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (49/128:ℝ) left_from cover_node_520 right_from cover_node_526

return_split cover_node_528 edge_at .oldSwitch box((23/64:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (3/8:ℝ) left_from cover_node_514 right_from cover_node_527

return_split cover_node_529 edge_at .oldSwitch box((25/64:ℝ),(401/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row533 right_from envelope_row534

return_split cover_node_530 edge_at .oldSwitch box((25/64:ℝ),(401/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row532 right_from cover_node_529

return_split cover_node_531 edge_at .oldSwitch box((25/64:ℝ),(401/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row535 right_from envelope_row536

return_split cover_node_532 edge_at .oldSwitch box((25/64:ℝ),(401/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row537 right_from envelope_row538

return_split cover_node_533 edge_at .oldSwitch box((25/64:ℝ),(401/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_531 right_from cover_node_532

return_split cover_node_534 edge_at .oldSwitch box((25/64:ℝ),(401/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_530 right_from cover_node_533

return_split cover_node_535 edge_at .oldSwitch box((401/1024:ℝ),(201/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row540 right_from envelope_row541

return_split cover_node_536 edge_at .oldSwitch box((401/1024:ℝ),(201/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row539 right_from cover_node_535

return_split cover_node_537 edge_at .oldSwitch box((401/1024:ℝ),(201/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row542 right_from envelope_row543

return_split cover_node_538 edge_at .oldSwitch box((401/1024:ℝ),(201/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row544 right_from envelope_row545

return_split cover_node_539 edge_at .oldSwitch box((401/1024:ℝ),(201/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_537 right_from cover_node_538

return_split cover_node_540 edge_at .oldSwitch box((401/1024:ℝ),(201/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_536 right_from cover_node_539

return_split cover_node_541 edge_at .oldSwitch box((25/64:ℝ),(201/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (401/1024:ℝ) left_from cover_node_534 right_from cover_node_540

return_split cover_node_542 edge_at .oldSwitch box((201/512:ℝ),(403/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row547 right_from envelope_row548

return_split cover_node_543 edge_at .oldSwitch box((201/512:ℝ),(403/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row546 right_from cover_node_542

return_split cover_node_544 edge_at .oldSwitch box((201/512:ℝ),(403/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row549 right_from envelope_row550

return_split cover_node_545 edge_at .oldSwitch box((201/512:ℝ),(403/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row551 right_from envelope_row552

return_split cover_node_546 edge_at .oldSwitch box((201/512:ℝ),(403/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_544 right_from cover_node_545

return_split cover_node_547 edge_at .oldSwitch box((201/512:ℝ),(403/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_543 right_from cover_node_546

return_split cover_node_548 edge_at .oldSwitch box((403/1024:ℝ),(101/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row554 right_from envelope_row555

return_split cover_node_549 edge_at .oldSwitch box((403/1024:ℝ),(101/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row553 right_from cover_node_548

return_split cover_node_550 edge_at .oldSwitch box((403/1024:ℝ),(101/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row556 right_from envelope_row557

return_split cover_node_551 edge_at .oldSwitch box((403/1024:ℝ),(101/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row558 right_from envelope_row559

return_split cover_node_552 edge_at .oldSwitch box((403/1024:ℝ),(101/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_550 right_from cover_node_551

return_split cover_node_553 edge_at .oldSwitch box((403/1024:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_549 right_from cover_node_552

return_split cover_node_554 edge_at .oldSwitch box((201/512:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (403/1024:ℝ) left_from cover_node_547 right_from cover_node_553

return_split cover_node_555 edge_at .oldSwitch box((25/64:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (201/512:ℝ) left_from cover_node_541 right_from cover_node_554

return_split cover_node_556 edge_at .oldSwitch box((23/64:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (25/64:ℝ) left_from cover_node_528 right_from cover_node_555

return_split cover_node_557 edge_at .oldSwitch box((0:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (23/64:ℝ) left_from cover_node_501 right_from cover_node_556

return_split cover_node_558 edge_at .oldSwitch box((101/256:ℝ),(405/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row561 right_from envelope_row562

return_split cover_node_559 edge_at .oldSwitch box((101/256:ℝ),(405/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row560 right_from cover_node_558

return_split cover_node_560 edge_at .oldSwitch box((101/256:ℝ),(405/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row563 right_from envelope_row564

return_split cover_node_561 edge_at .oldSwitch box((101/256:ℝ),(405/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row565 right_from envelope_row566

return_split cover_node_562 edge_at .oldSwitch box((101/256:ℝ),(405/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_560 right_from cover_node_561

return_split cover_node_563 edge_at .oldSwitch box((101/256:ℝ),(405/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_559 right_from cover_node_562

return_split cover_node_564 edge_at .oldSwitch box((405/1024:ℝ),(203/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row568 right_from envelope_row569

return_split cover_node_565 edge_at .oldSwitch box((405/1024:ℝ),(203/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row567 right_from cover_node_564

return_split cover_node_566 edge_at .oldSwitch box((405/1024:ℝ),(203/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row570 right_from envelope_row571

return_split cover_node_567 edge_at .oldSwitch box((405/1024:ℝ),(203/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row572 right_from envelope_row573

return_split cover_node_568 edge_at .oldSwitch box((405/1024:ℝ),(203/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_566 right_from cover_node_567

return_split cover_node_569 edge_at .oldSwitch box((405/1024:ℝ),(203/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_565 right_from cover_node_568

return_split cover_node_570 edge_at .oldSwitch box((101/256:ℝ),(203/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (405/1024:ℝ) left_from cover_node_563 right_from cover_node_569

return_split cover_node_571 edge_at .oldSwitch box((203/512:ℝ),(407/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row575 right_from envelope_row576

return_split cover_node_572 edge_at .oldSwitch box((203/512:ℝ),(407/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row574 right_from cover_node_571

return_split cover_node_573 edge_at .oldSwitch box((203/512:ℝ),(407/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row577 right_from envelope_row578

return_split cover_node_574 edge_at .oldSwitch box((203/512:ℝ),(407/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row579 right_from envelope_row580

return_split cover_node_575 edge_at .oldSwitch box((203/512:ℝ),(407/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_573 right_from cover_node_574

return_split cover_node_576 edge_at .oldSwitch box((203/512:ℝ),(407/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_572 right_from cover_node_575

return_split cover_node_577 edge_at .oldSwitch box((407/1024:ℝ),(51/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row582 right_from envelope_row583

return_split cover_node_578 edge_at .oldSwitch box((407/1024:ℝ),(51/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row581 right_from cover_node_577

return_split cover_node_579 edge_at .oldSwitch box((407/1024:ℝ),(51/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row584 right_from envelope_row585

return_split cover_node_580 edge_at .oldSwitch box((407/1024:ℝ),(51/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row586 right_from envelope_row587

return_split cover_node_581 edge_at .oldSwitch box((407/1024:ℝ),(51/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_579 right_from cover_node_580

return_split cover_node_582 edge_at .oldSwitch box((407/1024:ℝ),(51/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_578 right_from cover_node_581

return_split cover_node_583 edge_at .oldSwitch box((203/512:ℝ),(51/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (407/1024:ℝ) left_from cover_node_576 right_from cover_node_582

return_split cover_node_584 edge_at .oldSwitch box((101/256:ℝ),(51/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (203/512:ℝ) left_from cover_node_570 right_from cover_node_583

return_split cover_node_585 edge_at .oldSwitch box((51/128:ℝ),(13/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row589 right_from envelope_row590

return_split cover_node_586 edge_at .oldSwitch box((51/128:ℝ),(13/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row588 right_from cover_node_585

return_split cover_node_587 edge_at .oldSwitch box((51/128:ℝ),(13/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row591 right_from envelope_row592

return_split cover_node_588 edge_at .oldSwitch box((51/128:ℝ),(13/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row593 right_from envelope_row594

return_split cover_node_589 edge_at .oldSwitch box((51/128:ℝ),(13/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_587 right_from cover_node_588

return_split cover_node_590 edge_at .oldSwitch box((51/128:ℝ),(13/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_586 right_from cover_node_589

return_split cover_node_591 edge_at .oldSwitch box((13/32:ℝ),(417/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row596 right_from envelope_row597

return_split cover_node_592 edge_at .oldSwitch box((13/32:ℝ),(417/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row595 right_from cover_node_591

return_split cover_node_593 edge_at .oldSwitch box((13/32:ℝ),(417/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row598 right_from envelope_row599

return_split cover_node_594 edge_at .oldSwitch box((13/32:ℝ),(417/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row600 right_from envelope_row601

return_split cover_node_595 edge_at .oldSwitch box((13/32:ℝ),(417/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_593 right_from cover_node_594

return_split cover_node_596 edge_at .oldSwitch box((13/32:ℝ),(417/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_592 right_from cover_node_595

return_split cover_node_597 edge_at .oldSwitch box((51/128:ℝ),(417/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (13/32:ℝ) left_from cover_node_590 right_from cover_node_596

return_split cover_node_598 edge_at .oldSwitch box((417/1024:ℝ),(209/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row603 right_from envelope_row604

return_split cover_node_599 edge_at .oldSwitch box((417/1024:ℝ),(209/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row602 right_from cover_node_598

return_split cover_node_600 edge_at .oldSwitch box((417/1024:ℝ),(209/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row605 right_from envelope_row606

return_split cover_node_601 edge_at .oldSwitch box((417/1024:ℝ),(209/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row607 right_from envelope_row608

return_split cover_node_602 edge_at .oldSwitch box((417/1024:ℝ),(209/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_600 right_from cover_node_601

return_split cover_node_603 edge_at .oldSwitch box((417/1024:ℝ),(209/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_599 right_from cover_node_602

return_split cover_node_604 edge_at .oldSwitch box((209/512:ℝ),(419/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row610 right_from envelope_row611

return_split cover_node_605 edge_at .oldSwitch box((209/512:ℝ),(419/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row609 right_from cover_node_604

return_split cover_node_606 edge_at .oldSwitch box((209/512:ℝ),(419/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row612 right_from envelope_row613

return_split cover_node_607 edge_at .oldSwitch box((209/512:ℝ),(419/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row614 right_from envelope_row615

return_split cover_node_608 edge_at .oldSwitch box((209/512:ℝ),(419/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_606 right_from cover_node_607

return_split cover_node_609 edge_at .oldSwitch box((209/512:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_605 right_from cover_node_608

return_split cover_node_610 edge_at .oldSwitch box((417/1024:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (209/512:ℝ) left_from cover_node_603 right_from cover_node_609

return_split cover_node_611 edge_at .oldSwitch box((51/128:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (417/1024:ℝ) left_from cover_node_597 right_from cover_node_610

return_split cover_node_612 edge_at .oldSwitch box((101/256:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (51/128:ℝ) left_from cover_node_584 right_from cover_node_611

return_split cover_node_613 edge_at .oldSwitch box((419/1024:ℝ),(105/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row617 right_from envelope_row618

return_split cover_node_614 edge_at .oldSwitch box((419/1024:ℝ),(105/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row616 right_from cover_node_613

return_split cover_node_615 edge_at .oldSwitch box((419/1024:ℝ),(105/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row619 right_from envelope_row620

return_split cover_node_616 edge_at .oldSwitch box((419/1024:ℝ),(105/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row621 right_from envelope_row622

return_split cover_node_617 edge_at .oldSwitch box((419/1024:ℝ),(105/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_615 right_from cover_node_616

return_split cover_node_618 edge_at .oldSwitch box((419/1024:ℝ),(105/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_614 right_from cover_node_617

return_split cover_node_619 edge_at .oldSwitch box((105/256:ℝ),(421/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row624 right_from envelope_row625

return_split cover_node_620 edge_at .oldSwitch box((105/256:ℝ),(421/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row623 right_from cover_node_619

return_split cover_node_621 edge_at .oldSwitch box((105/256:ℝ),(421/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row626 right_from envelope_row627

return_split cover_node_622 edge_at .oldSwitch box((105/256:ℝ),(421/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row628 right_from envelope_row629

return_split cover_node_623 edge_at .oldSwitch box((105/256:ℝ),(421/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_621 right_from cover_node_622

return_split cover_node_624 edge_at .oldSwitch box((105/256:ℝ),(421/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_620 right_from cover_node_623

return_split cover_node_625 edge_at .oldSwitch box((419/1024:ℝ),(421/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (105/256:ℝ) left_from cover_node_618 right_from cover_node_624

return_split cover_node_626 edge_at .oldSwitch box((421/1024:ℝ),(211/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row631 right_from envelope_row632

return_split cover_node_627 edge_at .oldSwitch box((421/1024:ℝ),(211/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row630 right_from cover_node_626

return_split cover_node_628 edge_at .oldSwitch box((421/1024:ℝ),(211/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row633 right_from envelope_row634

return_split cover_node_629 edge_at .oldSwitch box((421/1024:ℝ),(211/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row635 right_from envelope_row636

return_split cover_node_630 edge_at .oldSwitch box((421/1024:ℝ),(211/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_628 right_from cover_node_629

return_split cover_node_631 edge_at .oldSwitch box((421/1024:ℝ),(211/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_627 right_from cover_node_630

return_split cover_node_632 edge_at .oldSwitch box((211/512:ℝ),(423/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row638 right_from envelope_row639

return_split cover_node_633 edge_at .oldSwitch box((211/512:ℝ),(423/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row637 right_from cover_node_632

return_split cover_node_634 edge_at .oldSwitch box((211/512:ℝ),(423/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row640 right_from envelope_row641

return_split cover_node_635 edge_at .oldSwitch box((211/512:ℝ),(423/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row642 right_from envelope_row643

return_split cover_node_636 edge_at .oldSwitch box((211/512:ℝ),(423/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_634 right_from cover_node_635

return_split cover_node_637 edge_at .oldSwitch box((211/512:ℝ),(423/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_633 right_from cover_node_636

return_split cover_node_638 edge_at .oldSwitch box((421/1024:ℝ),(423/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (211/512:ℝ) left_from cover_node_631 right_from cover_node_637

return_split cover_node_639 edge_at .oldSwitch box((419/1024:ℝ),(423/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (421/1024:ℝ) left_from cover_node_625 right_from cover_node_638

return_split cover_node_640 edge_at .oldSwitch box((423/1024:ℝ),(53/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row645 right_from envelope_row646

return_split cover_node_641 edge_at .oldSwitch box((423/1024:ℝ),(53/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row644 right_from cover_node_640

return_split cover_node_642 edge_at .oldSwitch box((423/1024:ℝ),(53/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row647 right_from envelope_row648

return_split cover_node_643 edge_at .oldSwitch box((423/1024:ℝ),(53/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row649 right_from envelope_row650

return_split cover_node_644 edge_at .oldSwitch box((423/1024:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_642 right_from cover_node_643

return_split cover_node_645 edge_at .oldSwitch box((423/1024:ℝ),(53/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_641 right_from cover_node_644

return_split cover_node_646 edge_at .oldSwitch box((53/128:ℝ),(425/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row652 right_from envelope_row653

return_split cover_node_647 edge_at .oldSwitch box((53/128:ℝ),(425/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row651 right_from cover_node_646

return_split cover_node_648 edge_at .oldSwitch box((53/128:ℝ),(425/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row654 right_from envelope_row655

return_split cover_node_649 edge_at .oldSwitch box((53/128:ℝ),(425/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row656 right_from envelope_row657

return_split cover_node_650 edge_at .oldSwitch box((53/128:ℝ),(425/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_648 right_from cover_node_649

return_split cover_node_651 edge_at .oldSwitch box((53/128:ℝ),(425/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_647 right_from cover_node_650

return_split cover_node_652 edge_at .oldSwitch box((423/1024:ℝ),(425/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (53/128:ℝ) left_from cover_node_645 right_from cover_node_651

return_split cover_node_653 edge_at .oldSwitch box((425/1024:ℝ),(213/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row659 right_from envelope_row660

return_split cover_node_654 edge_at .oldSwitch box((425/1024:ℝ),(213/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row658 right_from cover_node_653

return_split cover_node_655 edge_at .oldSwitch box((425/1024:ℝ),(213/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row661 right_from envelope_row662

return_split cover_node_656 edge_at .oldSwitch box((425/1024:ℝ),(213/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row663 right_from envelope_row664

return_split cover_node_657 edge_at .oldSwitch box((425/1024:ℝ),(213/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_655 right_from cover_node_656

return_split cover_node_658 edge_at .oldSwitch box((425/1024:ℝ),(213/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_654 right_from cover_node_657

return_split cover_node_659 edge_at .oldSwitch box((213/512:ℝ),(427/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row666 right_from envelope_row667

return_split cover_node_660 edge_at .oldSwitch box((213/512:ℝ),(427/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row665 right_from cover_node_659

return_split cover_node_661 edge_at .oldSwitch box((213/512:ℝ),(427/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row668 right_from envelope_row669

return_split cover_node_662 edge_at .oldSwitch box((213/512:ℝ),(427/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row670 right_from envelope_row671

return_split cover_node_663 edge_at .oldSwitch box((213/512:ℝ),(427/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_661 right_from cover_node_662

return_split cover_node_664 edge_at .oldSwitch box((213/512:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_660 right_from cover_node_663

return_split cover_node_665 edge_at .oldSwitch box((425/1024:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (213/512:ℝ) left_from cover_node_658 right_from cover_node_664

return_split cover_node_666 edge_at .oldSwitch box((423/1024:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (425/1024:ℝ) left_from cover_node_652 right_from cover_node_665

return_split cover_node_667 edge_at .oldSwitch box((419/1024:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (423/1024:ℝ) left_from cover_node_639 right_from cover_node_666

return_split cover_node_668 edge_at .oldSwitch box((101/256:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (419/1024:ℝ) left_from cover_node_612 right_from cover_node_667

return_split cover_node_669 edge_at .oldSwitch box((0:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (101/256:ℝ) left_from cover_node_557 right_from cover_node_668

return_split cover_node_670 edge_at .oldSwitch box((427/1024:ℝ),(107/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row673 right_from envelope_row674

return_split cover_node_671 edge_at .oldSwitch box((427/1024:ℝ),(107/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row672 right_from cover_node_670

return_split cover_node_672 edge_at .oldSwitch box((427/1024:ℝ),(107/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row675 right_from envelope_row676

return_split cover_node_673 edge_at .oldSwitch box((427/1024:ℝ),(107/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row677 right_from envelope_row678

return_split cover_node_674 edge_at .oldSwitch box((427/1024:ℝ),(107/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_672 right_from cover_node_673

return_split cover_node_675 edge_at .oldSwitch box((427/1024:ℝ),(107/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_671 right_from cover_node_674

return_split cover_node_676 edge_at .oldSwitch box((107/256:ℝ),(429/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row680 right_from envelope_row681

return_split cover_node_677 edge_at .oldSwitch box((107/256:ℝ),(429/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row679 right_from cover_node_676

return_split cover_node_678 edge_at .oldSwitch box((107/256:ℝ),(429/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row682 right_from envelope_row683

return_split cover_node_679 edge_at .oldSwitch box((107/256:ℝ),(429/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row684 right_from envelope_row685

return_split cover_node_680 edge_at .oldSwitch box((107/256:ℝ),(429/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_678 right_from cover_node_679

return_split cover_node_681 edge_at .oldSwitch box((107/256:ℝ),(429/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_677 right_from cover_node_680

return_split cover_node_682 edge_at .oldSwitch box((427/1024:ℝ),(429/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (107/256:ℝ) left_from cover_node_675 right_from cover_node_681

return_split cover_node_683 edge_at .oldSwitch box((429/1024:ℝ),(215/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row687 right_from envelope_row688

return_split cover_node_684 edge_at .oldSwitch box((429/1024:ℝ),(215/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row686 right_from cover_node_683

return_split cover_node_685 edge_at .oldSwitch box((429/1024:ℝ),(215/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row689 right_from envelope_row690

return_split cover_node_686 edge_at .oldSwitch box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row691 right_from envelope_row692

return_split cover_node_687 edge_at .oldSwitch box((429/1024:ℝ),(215/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_685 right_from cover_node_686

return_split cover_node_688 edge_at .oldSwitch box((429/1024:ℝ),(215/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_684 right_from cover_node_687

return_split cover_node_689 edge_at .oldSwitch box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row694 right_from envelope_row695

return_split cover_node_690 edge_at .oldSwitch box((215/512:ℝ),(431/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row693 right_from cover_node_689

return_split cover_node_691 edge_at .oldSwitch box((215/512:ℝ),(431/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row696 right_from envelope_row697

return_split cover_node_692 edge_at .oldSwitch box((215/512:ℝ),(431/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row698 right_from envelope_row699

return_split cover_node_693 edge_at .oldSwitch box((215/512:ℝ),(431/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_691 right_from cover_node_692

return_split cover_node_694 edge_at .oldSwitch box((215/512:ℝ),(431/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_690 right_from cover_node_693

return_split cover_node_695 edge_at .oldSwitch box((429/1024:ℝ),(431/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (215/512:ℝ) left_from cover_node_688 right_from cover_node_694

return_split cover_node_696 edge_at .oldSwitch box((427/1024:ℝ),(431/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (429/1024:ℝ) left_from cover_node_682 right_from cover_node_695

return_split cover_node_697 edge_at .oldSwitch box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row701 right_from envelope_row702

return_split cover_node_698 edge_at .oldSwitch box((431/1024:ℝ),(27/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row700 right_from cover_node_697

return_split cover_node_699 edge_at .oldSwitch box((431/1024:ℝ),(27/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row703 right_from envelope_row704

return_split cover_node_700 edge_at .oldSwitch box((431/1024:ℝ),(27/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row705 right_from envelope_row706

return_split cover_node_701 edge_at .oldSwitch box((431/1024:ℝ),(27/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_699 right_from cover_node_700

return_split cover_node_702 edge_at .oldSwitch box((431/1024:ℝ),(27/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_698 right_from cover_node_701

return_split cover_node_703 edge_at .oldSwitch box((27/64:ℝ),(433/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row708 right_from envelope_row709

return_split cover_node_704 edge_at .oldSwitch box((27/64:ℝ),(433/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row707 right_from cover_node_703

return_split cover_node_705 edge_at .oldSwitch box((27/64:ℝ),(433/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row710 right_from envelope_row711

return_split cover_node_706 edge_at .oldSwitch box((27/64:ℝ),(433/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row712 right_from envelope_row713

return_split cover_node_707 edge_at .oldSwitch box((27/64:ℝ),(433/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_705 right_from cover_node_706

return_split cover_node_708 edge_at .oldSwitch box((27/64:ℝ),(433/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_704 right_from cover_node_707

return_split cover_node_709 edge_at .oldSwitch box((431/1024:ℝ),(433/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (27/64:ℝ) left_from cover_node_702 right_from cover_node_708

return_split cover_node_710 edge_at .oldSwitch box((433/1024:ℝ),(217/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row715 right_from envelope_row716

return_split cover_node_711 edge_at .oldSwitch box((433/1024:ℝ),(217/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row714 right_from cover_node_710

return_split cover_node_712 edge_at .oldSwitch box((433/1024:ℝ),(217/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row717 right_from envelope_row718

return_split cover_node_713 edge_at .oldSwitch box((433/1024:ℝ),(217/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row719 right_from envelope_row720

return_split cover_node_714 edge_at .oldSwitch box((433/1024:ℝ),(217/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_712 right_from cover_node_713

return_split cover_node_715 edge_at .oldSwitch box((433/1024:ℝ),(217/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_711 right_from cover_node_714

return_split cover_node_716 edge_at .oldSwitch box((217/512:ℝ),(435/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row722 right_from envelope_row723

return_split cover_node_717 edge_at .oldSwitch box((217/512:ℝ),(435/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row721 right_from cover_node_716

return_split cover_node_718 edge_at .oldSwitch box((217/512:ℝ),(435/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row724 right_from envelope_row725

return_split cover_node_719 edge_at .oldSwitch box((217/512:ℝ),(435/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row726 right_from envelope_row727

return_split cover_node_720 edge_at .oldSwitch box((217/512:ℝ),(435/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_718 right_from cover_node_719

return_split cover_node_721 edge_at .oldSwitch box((217/512:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_717 right_from cover_node_720

return_split cover_node_722 edge_at .oldSwitch box((433/1024:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (217/512:ℝ) left_from cover_node_715 right_from cover_node_721

return_split cover_node_723 edge_at .oldSwitch box((431/1024:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (433/1024:ℝ) left_from cover_node_709 right_from cover_node_722

return_split cover_node_724 edge_at .oldSwitch box((427/1024:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (431/1024:ℝ) left_from cover_node_696 right_from cover_node_723

return_split cover_node_725 edge_at .oldSwitch box((435/1024:ℝ),(109/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row729 right_from envelope_row730

return_split cover_node_726 edge_at .oldSwitch box((435/1024:ℝ),(109/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row728 right_from cover_node_725

return_split cover_node_727 edge_at .oldSwitch box((435/1024:ℝ),(109/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row731 right_from envelope_row732

return_split cover_node_728 edge_at .oldSwitch box((435/1024:ℝ),(109/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row733 right_from envelope_row734

return_split cover_node_729 edge_at .oldSwitch box((435/1024:ℝ),(109/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_727 right_from cover_node_728

return_split cover_node_730 edge_at .oldSwitch box((435/1024:ℝ),(109/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_726 right_from cover_node_729

return_split cover_node_731 edge_at .oldSwitch box((109/256:ℝ),(437/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row736 right_from envelope_row737

return_split cover_node_732 edge_at .oldSwitch box((109/256:ℝ),(437/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row735 right_from cover_node_731

return_split cover_node_733 edge_at .oldSwitch box((109/256:ℝ),(437/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row738 right_from envelope_row739

return_split cover_node_734 edge_at .oldSwitch box((109/256:ℝ),(437/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row740 right_from envelope_row741

return_split cover_node_735 edge_at .oldSwitch box((109/256:ℝ),(437/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_733 right_from cover_node_734

return_split cover_node_736 edge_at .oldSwitch box((109/256:ℝ),(437/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_732 right_from cover_node_735

return_split cover_node_737 edge_at .oldSwitch box((435/1024:ℝ),(437/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (109/256:ℝ) left_from cover_node_730 right_from cover_node_736

return_split cover_node_738 edge_at .oldSwitch box((437/1024:ℝ),(219/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row743 right_from envelope_row744

return_split cover_node_739 edge_at .oldSwitch box((437/1024:ℝ),(219/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row742 right_from cover_node_738

return_split cover_node_740 edge_at .oldSwitch box((437/1024:ℝ),(219/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row745 right_from envelope_row746

return_split cover_node_741 edge_at .oldSwitch box((437/1024:ℝ),(219/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row747 right_from envelope_row748

return_split cover_node_742 edge_at .oldSwitch box((437/1024:ℝ),(219/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_740 right_from cover_node_741

return_split cover_node_743 edge_at .oldSwitch box((437/1024:ℝ),(219/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_739 right_from cover_node_742

return_split cover_node_744 edge_at .oldSwitch box((219/512:ℝ),(439/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row750 right_from envelope_row751

return_split cover_node_745 edge_at .oldSwitch box((219/512:ℝ),(439/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row749 right_from cover_node_744

return_split cover_node_746 edge_at .oldSwitch box((219/512:ℝ),(439/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row752 right_from envelope_row753

return_split cover_node_747 edge_at .oldSwitch box((219/512:ℝ),(439/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row754 right_from envelope_row755

return_split cover_node_748 edge_at .oldSwitch box((219/512:ℝ),(439/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_746 right_from cover_node_747

return_split cover_node_749 edge_at .oldSwitch box((219/512:ℝ),(439/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_745 right_from cover_node_748

return_split cover_node_750 edge_at .oldSwitch box((437/1024:ℝ),(439/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (219/512:ℝ) left_from cover_node_743 right_from cover_node_749

return_split cover_node_751 edge_at .oldSwitch box((435/1024:ℝ),(439/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (437/1024:ℝ) left_from cover_node_737 right_from cover_node_750

return_split cover_node_752 edge_at .oldSwitch box((439/1024:ℝ),(55/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row757 right_from envelope_row758

return_split cover_node_753 edge_at .oldSwitch box((439/1024:ℝ),(55/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row756 right_from cover_node_752

return_split cover_node_754 edge_at .oldSwitch box((439/1024:ℝ),(55/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row759 right_from envelope_row760

return_split cover_node_755 edge_at .oldSwitch box((439/1024:ℝ),(55/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row761 right_from envelope_row762

return_split cover_node_756 edge_at .oldSwitch box((439/1024:ℝ),(55/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_754 right_from cover_node_755

return_split cover_node_757 edge_at .oldSwitch box((439/1024:ℝ),(55/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_753 right_from cover_node_756

return_split cover_node_758 edge_at .oldSwitch box((55/128:ℝ),(111/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row764 right_from envelope_row765

return_split cover_node_759 edge_at .oldSwitch box((55/128:ℝ),(111/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row763 right_from cover_node_758

return_split cover_node_760 edge_at .oldSwitch box((55/128:ℝ),(111/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row766 right_from envelope_row767

return_split cover_node_761 edge_at .oldSwitch box((55/128:ℝ),(111/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row768 right_from envelope_row769

return_split cover_node_762 edge_at .oldSwitch box((55/128:ℝ),(111/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_760 right_from cover_node_761

return_split cover_node_763 edge_at .oldSwitch box((55/128:ℝ),(111/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_759 right_from cover_node_762

return_split cover_node_764 edge_at .oldSwitch box((439/1024:ℝ),(111/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (55/128:ℝ) left_from cover_node_757 right_from cover_node_763

return_split cover_node_765 edge_at .oldSwitch box((111/256:ℝ),(7/16:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row771 right_from envelope_row772

return_split cover_node_766 edge_at .oldSwitch box((111/256:ℝ),(7/16:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row770 right_from cover_node_765

return_split cover_node_767 edge_at .oldSwitch box((111/256:ℝ),(7/16:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row773 right_from envelope_row774

return_split cover_node_768 edge_at .oldSwitch box((111/256:ℝ),(7/16:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row775 right_from envelope_row776

return_split cover_node_769 edge_at .oldSwitch box((111/256:ℝ),(7/16:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_767 right_from cover_node_768

return_split cover_node_770 edge_at .oldSwitch box((111/256:ℝ),(7/16:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_766 right_from cover_node_769

return_split cover_node_771 edge_at .oldSwitch box((7/16:ℝ),(225/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row778 right_from envelope_row779

return_split cover_node_772 edge_at .oldSwitch box((7/16:ℝ),(225/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row777 right_from cover_node_771

return_split cover_node_773 edge_at .oldSwitch box((7/16:ℝ),(225/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row780 right_from envelope_row781

return_split cover_node_774 edge_at .oldSwitch box((7/16:ℝ),(225/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row782 right_from envelope_row783

return_split cover_node_775 edge_at .oldSwitch box((7/16:ℝ),(225/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_773 right_from cover_node_774

return_split cover_node_776 edge_at .oldSwitch box((7/16:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_772 right_from cover_node_775

return_split cover_node_777 edge_at .oldSwitch box((111/256:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (7/16:ℝ) left_from cover_node_770 right_from cover_node_776

return_split cover_node_778 edge_at .oldSwitch box((439/1024:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (111/256:ℝ) left_from cover_node_764 right_from cover_node_777

return_split cover_node_779 edge_at .oldSwitch box((435/1024:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (439/1024:ℝ) left_from cover_node_751 right_from cover_node_778

return_split cover_node_780 edge_at .oldSwitch box((427/1024:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (435/1024:ℝ) left_from cover_node_724 right_from cover_node_779

return_split cover_node_781 edge_at .oldSwitch box((225/512:ℝ),(453/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row785 right_from envelope_row786

return_split cover_node_782 edge_at .oldSwitch box((225/512:ℝ),(453/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row784 right_from cover_node_781

return_split cover_node_783 edge_at .oldSwitch box((225/512:ℝ),(453/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row787 right_from envelope_row788

return_split cover_node_784 edge_at .oldSwitch box((225/512:ℝ),(453/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row789 right_from envelope_row790

return_split cover_node_785 edge_at .oldSwitch box((225/512:ℝ),(453/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_783 right_from cover_node_784

return_split cover_node_786 edge_at .oldSwitch box((225/512:ℝ),(453/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_782 right_from cover_node_785

return_split cover_node_787 edge_at .oldSwitch box((453/1024:ℝ),(57/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row792 right_from envelope_row793

return_split cover_node_788 edge_at .oldSwitch box((453/1024:ℝ),(57/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row791 right_from cover_node_787

return_split cover_node_789 edge_at .oldSwitch box((453/1024:ℝ),(57/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row794 right_from envelope_row795

return_split cover_node_790 edge_at .oldSwitch box((453/1024:ℝ),(57/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row796 right_from envelope_row797

return_split cover_node_791 edge_at .oldSwitch box((453/1024:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_789 right_from cover_node_790

return_split cover_node_792 edge_at .oldSwitch box((453/1024:ℝ),(57/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_788 right_from cover_node_791

return_split cover_node_793 edge_at .oldSwitch box((225/512:ℝ),(57/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (453/1024:ℝ) left_from cover_node_786 right_from cover_node_792

return_split cover_node_794 edge_at .oldSwitch box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row799 right_from envelope_row800

return_split cover_node_795 edge_at .oldSwitch box((57/128:ℝ),(29/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row798 right_from cover_node_794

return_split cover_node_796 edge_at .oldSwitch box((57/128:ℝ),(29/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row801 right_from envelope_row802

return_split cover_node_797 edge_at .oldSwitch box((57/128:ℝ),(29/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row803 right_from envelope_row804

return_split cover_node_798 edge_at .oldSwitch box((57/128:ℝ),(29/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_796 right_from cover_node_797

return_split cover_node_799 edge_at .oldSwitch box((57/128:ℝ),(29/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_795 right_from cover_node_798

return_split cover_node_800 edge_at .oldSwitch box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row806 right_from envelope_row807

return_split cover_node_801 edge_at .oldSwitch box((29/64:ℝ),(59/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row805 right_from cover_node_800

return_split cover_node_802 edge_at .oldSwitch box((29/64:ℝ),(59/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row808 right_from envelope_row809

return_split cover_node_803 edge_at .oldSwitch box((29/64:ℝ),(59/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row810 right_from envelope_row811

return_split cover_node_804 edge_at .oldSwitch box((29/64:ℝ),(59/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_802 right_from cover_node_803

return_split cover_node_805 edge_at .oldSwitch box((29/64:ℝ),(59/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_801 right_from cover_node_804

return_split cover_node_806 edge_at .oldSwitch box((57/128:ℝ),(59/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (29/64:ℝ) left_from cover_node_799 right_from cover_node_805

return_split cover_node_807 edge_at .oldSwitch box((225/512:ℝ),(59/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (57/128:ℝ) left_from cover_node_793 right_from cover_node_806

return_split cover_node_808 edge_at .oldSwitch box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row813 right_from envelope_row814

return_split cover_node_809 edge_at .oldSwitch box((59/128:ℝ),(15/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row812 right_from cover_node_808

return_split cover_node_810 edge_at .oldSwitch box((59/128:ℝ),(15/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row815 right_from envelope_row816

return_split cover_node_811 edge_at .oldSwitch box((59/128:ℝ),(15/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row817 right_from envelope_row818

return_split cover_node_812 edge_at .oldSwitch box((59/128:ℝ),(15/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_810 right_from cover_node_811

return_split cover_node_813 edge_at .oldSwitch box((59/128:ℝ),(15/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_809 right_from cover_node_812

return_split cover_node_814 edge_at .oldSwitch box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row820 right_from envelope_row821

return_split cover_node_815 edge_at .oldSwitch box((15/32:ℝ),(61/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row819 right_from cover_node_814

return_split cover_node_816 edge_at .oldSwitch box((15/32:ℝ),(61/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row822 right_from envelope_row823

return_split cover_node_817 edge_at .oldSwitch box((15/32:ℝ),(61/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row824 right_from envelope_row825

return_split cover_node_818 edge_at .oldSwitch box((15/32:ℝ),(61/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_816 right_from cover_node_817

return_split cover_node_819 edge_at .oldSwitch box((15/32:ℝ),(61/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_815 right_from cover_node_818

return_split cover_node_820 edge_at .oldSwitch box((59/128:ℝ),(61/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (15/32:ℝ) left_from cover_node_813 right_from cover_node_819

return_split cover_node_821 edge_at .oldSwitch box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row827 right_from envelope_row828

return_split cover_node_822 edge_at .oldSwitch box((61/128:ℝ),(31/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row826 right_from cover_node_821

return_split cover_node_823 edge_at .oldSwitch box((61/128:ℝ),(31/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row829 right_from envelope_row830

return_split cover_node_824 edge_at .oldSwitch box((61/128:ℝ),(31/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row831 right_from envelope_row832

return_split cover_node_825 edge_at .oldSwitch box((61/128:ℝ),(31/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_823 right_from cover_node_824

return_split cover_node_826 edge_at .oldSwitch box((61/128:ℝ),(31/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_822 right_from cover_node_825

return_split cover_node_827 edge_at .oldSwitch box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row834 right_from envelope_row835

return_split cover_node_828 edge_at .oldSwitch box((31/64:ℝ),(63/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row833 right_from cover_node_827

return_split cover_node_829 edge_at .oldSwitch box((31/64:ℝ),(63/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row836 right_from envelope_row837

return_split cover_node_830 edge_at .oldSwitch box((31/64:ℝ),(63/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row838 right_from envelope_row839

return_split cover_node_831 edge_at .oldSwitch box((31/64:ℝ),(63/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_829 right_from cover_node_830

return_split cover_node_832 edge_at .oldSwitch box((31/64:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_828 right_from cover_node_831

return_split cover_node_833 edge_at .oldSwitch box((61/128:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (31/64:ℝ) left_from cover_node_826 right_from cover_node_832

return_split cover_node_834 edge_at .oldSwitch box((59/128:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (61/128:ℝ) left_from cover_node_820 right_from cover_node_833

return_split cover_node_835 edge_at .oldSwitch box((225/512:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (59/128:ℝ) left_from cover_node_807 right_from cover_node_834

return_split cover_node_836 edge_at .oldSwitch box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row841 right_from envelope_row842

return_split cover_node_837 edge_at .oldSwitch box((63/128:ℝ),(1/2:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row840 right_from cover_node_836

return_split cover_node_838 edge_at .oldSwitch box((63/128:ℝ),(1/2:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row843 right_from envelope_row844

return_split cover_node_839 edge_at .oldSwitch box((63/128:ℝ),(1/2:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row845 right_from envelope_row846

return_split cover_node_840 edge_at .oldSwitch box((63/128:ℝ),(1/2:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_838 right_from cover_node_839

return_split cover_node_841 edge_at .oldSwitch box((63/128:ℝ),(1/2:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_837 right_from cover_node_840

return_split cover_node_842 edge_at .oldSwitch box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row848 right_from envelope_row849

return_split cover_node_843 edge_at .oldSwitch box((1/2:ℝ),(65/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row847 right_from cover_node_842

return_split cover_node_844 edge_at .oldSwitch box((1/2:ℝ),(65/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row850 right_from envelope_row851

return_split cover_node_845 edge_at .oldSwitch box((1/2:ℝ),(65/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row852 right_from envelope_row853

return_split cover_node_846 edge_at .oldSwitch box((1/2:ℝ),(65/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_844 right_from cover_node_845

return_split cover_node_847 edge_at .oldSwitch box((1/2:ℝ),(65/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_843 right_from cover_node_846

return_split cover_node_848 edge_at .oldSwitch box((63/128:ℝ),(65/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (1/2:ℝ) left_from cover_node_841 right_from cover_node_847

return_split cover_node_849 edge_at .oldSwitch box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row855 right_from envelope_row856

return_split cover_node_850 edge_at .oldSwitch box((65/128:ℝ),(33/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row854 right_from cover_node_849

return_split cover_node_851 edge_at .oldSwitch box((65/128:ℝ),(33/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row857 right_from envelope_row858

return_split cover_node_852 edge_at .oldSwitch box((65/128:ℝ),(33/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row859 right_from envelope_row860

return_split cover_node_853 edge_at .oldSwitch box((65/128:ℝ),(33/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_851 right_from cover_node_852

return_split cover_node_854 edge_at .oldSwitch box((65/128:ℝ),(33/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_850 right_from cover_node_853

return_split cover_node_855 edge_at .oldSwitch box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row862 right_from envelope_row863

return_split cover_node_856 edge_at .oldSwitch box((33/64:ℝ),(67/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row861 right_from cover_node_855

return_split cover_node_857 edge_at .oldSwitch box((33/64:ℝ),(67/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row864 right_from envelope_row865

return_split cover_node_858 edge_at .oldSwitch box((33/64:ℝ),(67/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row866 right_from envelope_row867

return_split cover_node_859 edge_at .oldSwitch box((33/64:ℝ),(67/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_857 right_from cover_node_858

return_split cover_node_860 edge_at .oldSwitch box((33/64:ℝ),(67/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_856 right_from cover_node_859

return_split cover_node_861 edge_at .oldSwitch box((65/128:ℝ),(67/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (33/64:ℝ) left_from cover_node_854 right_from cover_node_860

return_split cover_node_862 edge_at .oldSwitch box((63/128:ℝ),(67/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (65/128:ℝ) left_from cover_node_848 right_from cover_node_861

return_split cover_node_863 edge_at .oldSwitch box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row869 right_from envelope_row870

return_split cover_node_864 edge_at .oldSwitch box((67/128:ℝ),(17/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row868 right_from cover_node_863

return_split cover_node_865 edge_at .oldSwitch box((67/128:ℝ),(17/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row871 right_from envelope_row872

return_split cover_node_866 edge_at .oldSwitch box((67/128:ℝ),(17/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row873 right_from envelope_row874

return_split cover_node_867 edge_at .oldSwitch box((67/128:ℝ),(17/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_865 right_from cover_node_866

return_split cover_node_868 edge_at .oldSwitch box((67/128:ℝ),(17/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_864 right_from cover_node_867

return_split cover_node_869 edge_at .oldSwitch box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row876 right_from envelope_row877

return_split cover_node_870 edge_at .oldSwitch box((17/32:ℝ),(69/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row875 right_from cover_node_869

return_split cover_node_871 edge_at .oldSwitch box((17/32:ℝ),(69/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row878 right_from envelope_row879

return_split cover_node_872 edge_at .oldSwitch box((17/32:ℝ),(69/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row880 right_from envelope_row881

return_split cover_node_873 edge_at .oldSwitch box((17/32:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_871 right_from cover_node_872

return_split cover_node_874 edge_at .oldSwitch box((17/32:ℝ),(69/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_870 right_from cover_node_873

return_split cover_node_875 edge_at .oldSwitch box((67/128:ℝ),(69/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (17/32:ℝ) left_from cover_node_868 right_from cover_node_874

return_split cover_node_876 edge_at .oldSwitch box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row883 right_from envelope_row884

return_split cover_node_877 edge_at .oldSwitch box((69/128:ℝ),(35/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row882 right_from cover_node_876

return_split cover_node_878 edge_at .oldSwitch box((69/128:ℝ),(35/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row885 right_from envelope_row886

return_split cover_node_879 edge_at .oldSwitch box((69/128:ℝ),(35/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row887 right_from envelope_row888

return_split cover_node_880 edge_at .oldSwitch box((69/128:ℝ),(35/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_878 right_from cover_node_879

return_split cover_node_881 edge_at .oldSwitch box((69/128:ℝ),(35/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_877 right_from cover_node_880

return_split cover_node_882 edge_at .oldSwitch box((35/64:ℝ),(3/4:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row890 right_from envelope_row891

return_split cover_node_883 edge_at .oldSwitch box((35/64:ℝ),(3/4:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row889 right_from cover_node_882

return_split cover_node_884 edge_at .oldSwitch box((35/64:ℝ),(3/4:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row892 right_from envelope_row893

return_split cover_node_885 edge_at .oldSwitch box((35/64:ℝ),(3/4:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row894 right_from envelope_row895

return_split cover_node_886 edge_at .oldSwitch box((35/64:ℝ),(3/4:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_884 right_from cover_node_885

return_split cover_node_887 edge_at .oldSwitch box((35/64:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_883 right_from cover_node_886

return_split cover_node_888 edge_at .oldSwitch box((69/128:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (35/64:ℝ) left_from cover_node_881 right_from cover_node_887

return_split cover_node_889 edge_at .oldSwitch box((67/128:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (69/128:ℝ) left_from cover_node_875 right_from cover_node_888

return_split cover_node_890 edge_at .oldSwitch box((63/128:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (67/128:ℝ) left_from cover_node_862 right_from cover_node_889

return_split cover_node_891 edge_at .oldSwitch box((225/512:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (63/128:ℝ) left_from cover_node_835 right_from cover_node_890

return_split cover_node_892 edge_at .oldSwitch box((427/1024:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (225/512:ℝ) left_from cover_node_780 right_from cover_node_891

return_split cover_node_893 edge_at .oldSwitch box((0:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (427/1024:ℝ) left_from cover_node_669 right_from cover_node_892

return_split cover_node_894 edge_at .newSwitch box((0:ℝ),(9/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row897 right_from envelope_row898

return_split cover_node_895 edge_at .newSwitch box((0:ℝ),(9/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row896 right_from cover_node_894

return_split cover_node_896 edge_at .newSwitch box((0:ℝ),(9/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row899 right_from envelope_row900

return_split cover_node_897 edge_at .newSwitch box((0:ℝ),(9/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row901 right_from envelope_row902

return_split cover_node_898 edge_at .newSwitch box((0:ℝ),(9/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_896 right_from cover_node_897

return_split cover_node_899 edge_at .newSwitch box((0:ℝ),(9/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_895 right_from cover_node_898

return_split cover_node_900 edge_at .newSwitch box((9/32:ℝ),(5/16:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row904 right_from envelope_row905

return_split cover_node_901 edge_at .newSwitch box((9/32:ℝ),(5/16:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row903 right_from cover_node_900

return_split cover_node_902 edge_at .newSwitch box((9/32:ℝ),(5/16:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row906 right_from envelope_row907

return_split cover_node_903 edge_at .newSwitch box((9/32:ℝ),(5/16:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row908 right_from envelope_row909

return_split cover_node_904 edge_at .newSwitch box((9/32:ℝ),(5/16:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_902 right_from cover_node_903

return_split cover_node_905 edge_at .newSwitch box((9/32:ℝ),(5/16:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_901 right_from cover_node_904

return_split cover_node_906 edge_at .newSwitch box((0:ℝ),(5/16:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (9/32:ℝ) left_from cover_node_899 right_from cover_node_905

return_split cover_node_907 edge_at .newSwitch box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row911 right_from envelope_row912

return_split cover_node_908 edge_at .newSwitch box((5/16:ℝ),(41/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row910 right_from cover_node_907

return_split cover_node_909 edge_at .newSwitch box((5/16:ℝ),(41/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row913 right_from envelope_row914

return_split cover_node_910 edge_at .newSwitch box((5/16:ℝ),(41/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row915 right_from envelope_row916

return_split cover_node_911 edge_at .newSwitch box((5/16:ℝ),(41/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_909 right_from cover_node_910

return_split cover_node_912 edge_at .newSwitch box((5/16:ℝ),(41/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_908 right_from cover_node_911

return_split cover_node_913 edge_at .newSwitch box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row918 right_from envelope_row919

return_split cover_node_914 edge_at .newSwitch box((41/128:ℝ),(21/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row917 right_from cover_node_913

return_split cover_node_915 edge_at .newSwitch box((41/128:ℝ),(21/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row920 right_from envelope_row921

return_split cover_node_916 edge_at .newSwitch box((41/128:ℝ),(21/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row922 right_from envelope_row923

return_split cover_node_917 edge_at .newSwitch box((41/128:ℝ),(21/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_915 right_from cover_node_916

return_split cover_node_918 edge_at .newSwitch box((41/128:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_914 right_from cover_node_917

return_split cover_node_919 edge_at .newSwitch box((5/16:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (41/128:ℝ) left_from cover_node_912 right_from cover_node_918

return_split cover_node_920 edge_at .newSwitch box((0:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (5/16:ℝ) left_from cover_node_906 right_from cover_node_919

return_split cover_node_921 edge_at .newSwitch box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row925 right_from envelope_row926

return_split cover_node_922 edge_at .newSwitch box((21/64:ℝ),(43/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row924 right_from cover_node_921

return_split cover_node_923 edge_at .newSwitch box((21/64:ℝ),(43/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row927 right_from envelope_row928

return_split cover_node_924 edge_at .newSwitch box((21/64:ℝ),(43/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row929 right_from envelope_row930

return_split cover_node_925 edge_at .newSwitch box((21/64:ℝ),(43/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_923 right_from cover_node_924

return_split cover_node_926 edge_at .newSwitch box((21/64:ℝ),(43/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_922 right_from cover_node_925

return_split cover_node_927 edge_at .newSwitch box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row932 right_from envelope_row933

return_split cover_node_928 edge_at .newSwitch box((43/128:ℝ),(11/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row931 right_from cover_node_927

return_split cover_node_929 edge_at .newSwitch box((43/128:ℝ),(11/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row934 right_from envelope_row935

return_split cover_node_930 edge_at .newSwitch box((43/128:ℝ),(11/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row936 right_from envelope_row937

return_split cover_node_931 edge_at .newSwitch box((43/128:ℝ),(11/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_929 right_from cover_node_930

return_split cover_node_932 edge_at .newSwitch box((43/128:ℝ),(11/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_928 right_from cover_node_931

return_split cover_node_933 edge_at .newSwitch box((21/64:ℝ),(11/32:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (43/128:ℝ) left_from cover_node_926 right_from cover_node_932

return_split cover_node_934 edge_at .newSwitch box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row939 right_from envelope_row940

return_split cover_node_935 edge_at .newSwitch box((11/32:ℝ),(45/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row938 right_from cover_node_934

return_split cover_node_936 edge_at .newSwitch box((11/32:ℝ),(45/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row941 right_from envelope_row942

return_split cover_node_937 edge_at .newSwitch box((11/32:ℝ),(45/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row943 right_from envelope_row944

return_split cover_node_938 edge_at .newSwitch box((11/32:ℝ),(45/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_936 right_from cover_node_937

return_split cover_node_939 edge_at .newSwitch box((11/32:ℝ),(45/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_935 right_from cover_node_938

return_split cover_node_940 edge_at .newSwitch box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row946 right_from envelope_row947

return_split cover_node_941 edge_at .newSwitch box((45/128:ℝ),(23/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row945 right_from cover_node_940

return_split cover_node_942 edge_at .newSwitch box((45/128:ℝ),(23/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row948 right_from envelope_row949

return_split cover_node_943 edge_at .newSwitch box((45/128:ℝ),(23/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row950 right_from envelope_row951

return_split cover_node_944 edge_at .newSwitch box((45/128:ℝ),(23/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_942 right_from cover_node_943

return_split cover_node_945 edge_at .newSwitch box((45/128:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_941 right_from cover_node_944

return_split cover_node_946 edge_at .newSwitch box((11/32:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (45/128:ℝ) left_from cover_node_939 right_from cover_node_945

return_split cover_node_947 edge_at .newSwitch box((21/64:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (11/32:ℝ) left_from cover_node_933 right_from cover_node_946

return_split cover_node_948 edge_at .newSwitch box((0:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (21/64:ℝ) left_from cover_node_920 right_from cover_node_947

return_split cover_node_949 edge_at .newSwitch box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row953 right_from envelope_row954

return_split cover_node_950 edge_at .newSwitch box((23/64:ℝ),(47/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row952 right_from cover_node_949

return_split cover_node_951 edge_at .newSwitch box((23/64:ℝ),(47/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row955 right_from envelope_row956

return_split cover_node_952 edge_at .newSwitch box((23/64:ℝ),(47/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row957 right_from envelope_row958

return_split cover_node_953 edge_at .newSwitch box((23/64:ℝ),(47/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_951 right_from cover_node_952

return_split cover_node_954 edge_at .newSwitch box((23/64:ℝ),(47/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_950 right_from cover_node_953

return_split cover_node_955 edge_at .newSwitch box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row960 right_from envelope_row961

return_split cover_node_956 edge_at .newSwitch box((47/128:ℝ),(3/8:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row959 right_from cover_node_955

return_split cover_node_957 edge_at .newSwitch box((47/128:ℝ),(3/8:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row962 right_from envelope_row963

return_split cover_node_958 edge_at .newSwitch box((47/128:ℝ),(3/8:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row964 right_from envelope_row965

return_split cover_node_959 edge_at .newSwitch box((47/128:ℝ),(3/8:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_957 right_from cover_node_958

return_split cover_node_960 edge_at .newSwitch box((47/128:ℝ),(3/8:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_956 right_from cover_node_959

return_split cover_node_961 edge_at .newSwitch box((23/64:ℝ),(3/8:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (47/128:ℝ) left_from cover_node_954 right_from cover_node_960

return_split cover_node_962 edge_at .newSwitch box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row967 right_from envelope_row968

return_split cover_node_963 edge_at .newSwitch box((3/8:ℝ),(49/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row966 right_from cover_node_962

return_split cover_node_964 edge_at .newSwitch box((3/8:ℝ),(49/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row969 right_from envelope_row970

return_split cover_node_965 edge_at .newSwitch box((3/8:ℝ),(49/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row971 right_from envelope_row972

return_split cover_node_966 edge_at .newSwitch box((3/8:ℝ),(49/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_964 right_from cover_node_965

return_split cover_node_967 edge_at .newSwitch box((3/8:ℝ),(49/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_963 right_from cover_node_966

return_split cover_node_968 edge_at .newSwitch box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row974 right_from envelope_row975

return_split cover_node_969 edge_at .newSwitch box((49/128:ℝ),(25/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row973 right_from cover_node_968

return_split cover_node_970 edge_at .newSwitch box((49/128:ℝ),(25/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row976 right_from envelope_row977

return_split cover_node_971 edge_at .newSwitch box((49/128:ℝ),(25/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row978 right_from envelope_row979

return_split cover_node_972 edge_at .newSwitch box((49/128:ℝ),(25/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_970 right_from cover_node_971

return_split cover_node_973 edge_at .newSwitch box((49/128:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_969 right_from cover_node_972

return_split cover_node_974 edge_at .newSwitch box((3/8:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (49/128:ℝ) left_from cover_node_967 right_from cover_node_973

return_split cover_node_975 edge_at .newSwitch box((23/64:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (3/8:ℝ) left_from cover_node_961 right_from cover_node_974

return_split cover_node_976 edge_at .newSwitch box((25/64:ℝ),(401/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row981 right_from envelope_row982

return_split cover_node_977 edge_at .newSwitch box((25/64:ℝ),(401/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row980 right_from cover_node_976

return_split cover_node_978 edge_at .newSwitch box((25/64:ℝ),(401/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row983 right_from envelope_row984

return_split cover_node_979 edge_at .newSwitch box((25/64:ℝ),(401/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row985 right_from envelope_row986

return_split cover_node_980 edge_at .newSwitch box((25/64:ℝ),(401/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_978 right_from cover_node_979

return_split cover_node_981 edge_at .newSwitch box((25/64:ℝ),(401/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_977 right_from cover_node_980

return_split cover_node_982 edge_at .newSwitch box((401/1024:ℝ),(201/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row988 right_from envelope_row989

return_split cover_node_983 edge_at .newSwitch box((401/1024:ℝ),(201/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row987 right_from cover_node_982

return_split cover_node_984 edge_at .newSwitch box((401/1024:ℝ),(201/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row990 right_from envelope_row991

return_split cover_node_985 edge_at .newSwitch box((401/1024:ℝ),(201/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row992 right_from envelope_row993

return_split cover_node_986 edge_at .newSwitch box((401/1024:ℝ),(201/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_984 right_from cover_node_985

return_split cover_node_987 edge_at .newSwitch box((401/1024:ℝ),(201/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_983 right_from cover_node_986

return_split cover_node_988 edge_at .newSwitch box((25/64:ℝ),(201/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (401/1024:ℝ) left_from cover_node_981 right_from cover_node_987

return_split cover_node_989 edge_at .newSwitch box((201/512:ℝ),(403/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row995 right_from envelope_row996

return_split cover_node_990 edge_at .newSwitch box((201/512:ℝ),(403/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row994 right_from cover_node_989

return_split cover_node_991 edge_at .newSwitch box((201/512:ℝ),(403/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row997 right_from envelope_row998

return_split cover_node_992 edge_at .newSwitch box((201/512:ℝ),(403/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row999 right_from envelope_row1000

return_split cover_node_993 edge_at .newSwitch box((201/512:ℝ),(403/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_991 right_from cover_node_992

return_split cover_node_994 edge_at .newSwitch box((201/512:ℝ),(403/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_990 right_from cover_node_993

return_split cover_node_995 edge_at .newSwitch box((403/1024:ℝ),(101/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1002 right_from envelope_row1003

return_split cover_node_996 edge_at .newSwitch box((403/1024:ℝ),(101/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1001 right_from cover_node_995

return_split cover_node_997 edge_at .newSwitch box((403/1024:ℝ),(101/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1004 right_from envelope_row1005

return_split cover_node_998 edge_at .newSwitch box((403/1024:ℝ),(101/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1006 right_from envelope_row1007

return_split cover_node_999 edge_at .newSwitch box((403/1024:ℝ),(101/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_997 right_from cover_node_998

return_split cover_node_1000 edge_at .newSwitch box((403/1024:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_996 right_from cover_node_999

return_split cover_node_1001 edge_at .newSwitch box((201/512:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (403/1024:ℝ) left_from cover_node_994 right_from cover_node_1000

return_split cover_node_1002 edge_at .newSwitch box((25/64:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (201/512:ℝ) left_from cover_node_988 right_from cover_node_1001

return_split cover_node_1003 edge_at .newSwitch box((23/64:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (25/64:ℝ) left_from cover_node_975 right_from cover_node_1002

return_split cover_node_1004 edge_at .newSwitch box((0:ℝ),(101/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (23/64:ℝ) left_from cover_node_948 right_from cover_node_1003

return_split cover_node_1005 edge_at .newSwitch box((101/256:ℝ),(405/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1009 right_from envelope_row1010

return_split cover_node_1006 edge_at .newSwitch box((101/256:ℝ),(405/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1008 right_from cover_node_1005

return_split cover_node_1007 edge_at .newSwitch box((101/256:ℝ),(405/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1011 right_from envelope_row1012

return_split cover_node_1008 edge_at .newSwitch box((101/256:ℝ),(405/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1013 right_from envelope_row1014

return_split cover_node_1009 edge_at .newSwitch box((101/256:ℝ),(405/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1007 right_from cover_node_1008

return_split cover_node_1010 edge_at .newSwitch box((101/256:ℝ),(405/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1006 right_from cover_node_1009

return_split cover_node_1011 edge_at .newSwitch box((405/1024:ℝ),(203/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1016 right_from envelope_row1017

return_split cover_node_1012 edge_at .newSwitch box((405/1024:ℝ),(203/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1015 right_from cover_node_1011

return_split cover_node_1013 edge_at .newSwitch box((405/1024:ℝ),(203/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1018 right_from envelope_row1019

return_split cover_node_1014 edge_at .newSwitch box((405/1024:ℝ),(203/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1020 right_from envelope_row1021

return_split cover_node_1015 edge_at .newSwitch box((405/1024:ℝ),(203/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1013 right_from cover_node_1014

return_split cover_node_1016 edge_at .newSwitch box((405/1024:ℝ),(203/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1012 right_from cover_node_1015

return_split cover_node_1017 edge_at .newSwitch box((101/256:ℝ),(203/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (405/1024:ℝ) left_from cover_node_1010 right_from cover_node_1016

return_split cover_node_1018 edge_at .newSwitch box((203/512:ℝ),(407/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1023 right_from envelope_row1024

return_split cover_node_1019 edge_at .newSwitch box((203/512:ℝ),(407/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1022 right_from cover_node_1018

return_split cover_node_1020 edge_at .newSwitch box((203/512:ℝ),(407/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1025 right_from envelope_row1026

return_split cover_node_1021 edge_at .newSwitch box((203/512:ℝ),(407/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1027 right_from envelope_row1028

return_split cover_node_1022 edge_at .newSwitch box((203/512:ℝ),(407/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1020 right_from cover_node_1021

return_split cover_node_1023 edge_at .newSwitch box((203/512:ℝ),(407/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1019 right_from cover_node_1022

return_split cover_node_1024 edge_at .newSwitch box((407/1024:ℝ),(51/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1030 right_from envelope_row1031

return_split cover_node_1025 edge_at .newSwitch box((407/1024:ℝ),(51/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1029 right_from cover_node_1024

return_split cover_node_1026 edge_at .newSwitch box((407/1024:ℝ),(51/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1032 right_from envelope_row1033

return_split cover_node_1027 edge_at .newSwitch box((407/1024:ℝ),(51/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1034 right_from envelope_row1035

return_split cover_node_1028 edge_at .newSwitch box((407/1024:ℝ),(51/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1026 right_from cover_node_1027

return_split cover_node_1029 edge_at .newSwitch box((407/1024:ℝ),(51/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1025 right_from cover_node_1028

return_split cover_node_1030 edge_at .newSwitch box((203/512:ℝ),(51/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (407/1024:ℝ) left_from cover_node_1023 right_from cover_node_1029

return_split cover_node_1031 edge_at .newSwitch box((101/256:ℝ),(51/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (203/512:ℝ) left_from cover_node_1017 right_from cover_node_1030

return_split cover_node_1032 edge_at .newSwitch box((51/128:ℝ),(13/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1037 right_from envelope_row1038

return_split cover_node_1033 edge_at .newSwitch box((51/128:ℝ),(13/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1036 right_from cover_node_1032

return_split cover_node_1034 edge_at .newSwitch box((51/128:ℝ),(13/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1039 right_from envelope_row1040

return_split cover_node_1035 edge_at .newSwitch box((51/128:ℝ),(13/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1041 right_from envelope_row1042

return_split cover_node_1036 edge_at .newSwitch box((51/128:ℝ),(13/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1034 right_from cover_node_1035

return_split cover_node_1037 edge_at .newSwitch box((51/128:ℝ),(13/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1033 right_from cover_node_1036

return_split cover_node_1038 edge_at .newSwitch box((13/32:ℝ),(417/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1044 right_from envelope_row1045

return_split cover_node_1039 edge_at .newSwitch box((13/32:ℝ),(417/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1043 right_from cover_node_1038

return_split cover_node_1040 edge_at .newSwitch box((13/32:ℝ),(417/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1046 right_from envelope_row1047

return_split cover_node_1041 edge_at .newSwitch box((13/32:ℝ),(417/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1048 right_from envelope_row1049

return_split cover_node_1042 edge_at .newSwitch box((13/32:ℝ),(417/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1040 right_from cover_node_1041

return_split cover_node_1043 edge_at .newSwitch box((13/32:ℝ),(417/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1039 right_from cover_node_1042

return_split cover_node_1044 edge_at .newSwitch box((51/128:ℝ),(417/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (13/32:ℝ) left_from cover_node_1037 right_from cover_node_1043

return_split cover_node_1045 edge_at .newSwitch box((417/1024:ℝ),(209/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1051 right_from envelope_row1052

return_split cover_node_1046 edge_at .newSwitch box((417/1024:ℝ),(209/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1050 right_from cover_node_1045

return_split cover_node_1047 edge_at .newSwitch box((417/1024:ℝ),(209/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1053 right_from envelope_row1054

return_split cover_node_1048 edge_at .newSwitch box((417/1024:ℝ),(209/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1055 right_from envelope_row1056

return_split cover_node_1049 edge_at .newSwitch box((417/1024:ℝ),(209/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1047 right_from cover_node_1048

return_split cover_node_1050 edge_at .newSwitch box((417/1024:ℝ),(209/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1046 right_from cover_node_1049

return_split cover_node_1051 edge_at .newSwitch box((209/512:ℝ),(419/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1058 right_from envelope_row1059

return_split cover_node_1052 edge_at .newSwitch box((209/512:ℝ),(419/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1057 right_from cover_node_1051

return_split cover_node_1053 edge_at .newSwitch box((209/512:ℝ),(419/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1060 right_from envelope_row1061

return_split cover_node_1054 edge_at .newSwitch box((209/512:ℝ),(419/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1062 right_from envelope_row1063

return_split cover_node_1055 edge_at .newSwitch box((209/512:ℝ),(419/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1053 right_from cover_node_1054

return_split cover_node_1056 edge_at .newSwitch box((209/512:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1052 right_from cover_node_1055

return_split cover_node_1057 edge_at .newSwitch box((417/1024:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (209/512:ℝ) left_from cover_node_1050 right_from cover_node_1056

return_split cover_node_1058 edge_at .newSwitch box((51/128:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (417/1024:ℝ) left_from cover_node_1044 right_from cover_node_1057

return_split cover_node_1059 edge_at .newSwitch box((101/256:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (51/128:ℝ) left_from cover_node_1031 right_from cover_node_1058

return_split cover_node_1060 edge_at .newSwitch box((419/1024:ℝ),(105/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1065 right_from envelope_row1066

return_split cover_node_1061 edge_at .newSwitch box((419/1024:ℝ),(105/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1064 right_from cover_node_1060

return_split cover_node_1062 edge_at .newSwitch box((419/1024:ℝ),(105/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1067 right_from envelope_row1068

return_split cover_node_1063 edge_at .newSwitch box((419/1024:ℝ),(105/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1069 right_from envelope_row1070

return_split cover_node_1064 edge_at .newSwitch box((419/1024:ℝ),(105/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1062 right_from cover_node_1063

return_split cover_node_1065 edge_at .newSwitch box((419/1024:ℝ),(105/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1061 right_from cover_node_1064

return_split cover_node_1066 edge_at .newSwitch box((105/256:ℝ),(421/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1072 right_from envelope_row1073

return_split cover_node_1067 edge_at .newSwitch box((105/256:ℝ),(421/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1071 right_from cover_node_1066

return_split cover_node_1068 edge_at .newSwitch box((105/256:ℝ),(421/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1074 right_from envelope_row1075

return_split cover_node_1069 edge_at .newSwitch box((105/256:ℝ),(421/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1076 right_from envelope_row1077

return_split cover_node_1070 edge_at .newSwitch box((105/256:ℝ),(421/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1068 right_from cover_node_1069

return_split cover_node_1071 edge_at .newSwitch box((105/256:ℝ),(421/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1067 right_from cover_node_1070

return_split cover_node_1072 edge_at .newSwitch box((419/1024:ℝ),(421/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (105/256:ℝ) left_from cover_node_1065 right_from cover_node_1071

return_split cover_node_1073 edge_at .newSwitch box((421/1024:ℝ),(211/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1079 right_from envelope_row1080

return_split cover_node_1074 edge_at .newSwitch box((421/1024:ℝ),(211/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1078 right_from cover_node_1073

return_split cover_node_1075 edge_at .newSwitch box((421/1024:ℝ),(211/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1081 right_from envelope_row1082

return_split cover_node_1076 edge_at .newSwitch box((421/1024:ℝ),(211/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1083 right_from envelope_row1084

return_split cover_node_1077 edge_at .newSwitch box((421/1024:ℝ),(211/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1075 right_from cover_node_1076

return_split cover_node_1078 edge_at .newSwitch box((421/1024:ℝ),(211/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1074 right_from cover_node_1077

return_split cover_node_1079 edge_at .newSwitch box((211/512:ℝ),(423/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1086 right_from envelope_row1087

return_split cover_node_1080 edge_at .newSwitch box((211/512:ℝ),(423/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1085 right_from cover_node_1079

return_split cover_node_1081 edge_at .newSwitch box((211/512:ℝ),(423/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1088 right_from envelope_row1089

return_split cover_node_1082 edge_at .newSwitch box((211/512:ℝ),(423/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1090 right_from envelope_row1091

return_split cover_node_1083 edge_at .newSwitch box((211/512:ℝ),(423/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1081 right_from cover_node_1082

return_split cover_node_1084 edge_at .newSwitch box((211/512:ℝ),(423/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1080 right_from cover_node_1083

return_split cover_node_1085 edge_at .newSwitch box((421/1024:ℝ),(423/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (211/512:ℝ) left_from cover_node_1078 right_from cover_node_1084

return_split cover_node_1086 edge_at .newSwitch box((419/1024:ℝ),(423/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (421/1024:ℝ) left_from cover_node_1072 right_from cover_node_1085

return_split cover_node_1087 edge_at .newSwitch box((423/1024:ℝ),(53/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1093 right_from envelope_row1094

return_split cover_node_1088 edge_at .newSwitch box((423/1024:ℝ),(53/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1092 right_from cover_node_1087

return_split cover_node_1089 edge_at .newSwitch box((423/1024:ℝ),(53/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1095 right_from envelope_row1096

return_split cover_node_1090 edge_at .newSwitch box((423/1024:ℝ),(53/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1097 right_from envelope_row1098

return_split cover_node_1091 edge_at .newSwitch box((423/1024:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1089 right_from cover_node_1090

return_split cover_node_1092 edge_at .newSwitch box((423/1024:ℝ),(53/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1088 right_from cover_node_1091

return_split cover_node_1093 edge_at .newSwitch box((53/128:ℝ),(425/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1100 right_from envelope_row1101

return_split cover_node_1094 edge_at .newSwitch box((53/128:ℝ),(425/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1099 right_from cover_node_1093

return_split cover_node_1095 edge_at .newSwitch box((53/128:ℝ),(425/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1102 right_from envelope_row1103

return_split cover_node_1096 edge_at .newSwitch box((53/128:ℝ),(425/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1104 right_from envelope_row1105

return_split cover_node_1097 edge_at .newSwitch box((53/128:ℝ),(425/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1095 right_from cover_node_1096

return_split cover_node_1098 edge_at .newSwitch box((53/128:ℝ),(425/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1094 right_from cover_node_1097

return_split cover_node_1099 edge_at .newSwitch box((423/1024:ℝ),(425/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (53/128:ℝ) left_from cover_node_1092 right_from cover_node_1098

return_split cover_node_1100 edge_at .newSwitch box((425/1024:ℝ),(213/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1107 right_from envelope_row1108

return_split cover_node_1101 edge_at .newSwitch box((425/1024:ℝ),(213/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1106 right_from cover_node_1100

return_split cover_node_1102 edge_at .newSwitch box((425/1024:ℝ),(213/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1109 right_from envelope_row1110

return_split cover_node_1103 edge_at .newSwitch box((425/1024:ℝ),(213/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1111 right_from envelope_row1112

return_split cover_node_1104 edge_at .newSwitch box((425/1024:ℝ),(213/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1102 right_from cover_node_1103

return_split cover_node_1105 edge_at .newSwitch box((425/1024:ℝ),(213/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1101 right_from cover_node_1104

return_split cover_node_1106 edge_at .newSwitch box((213/512:ℝ),(427/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1114 right_from envelope_row1115

return_split cover_node_1107 edge_at .newSwitch box((213/512:ℝ),(427/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1113 right_from cover_node_1106

return_split cover_node_1108 edge_at .newSwitch box((213/512:ℝ),(427/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1116 right_from envelope_row1117

return_split cover_node_1109 edge_at .newSwitch box((213/512:ℝ),(427/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1118 right_from envelope_row1119

return_split cover_node_1110 edge_at .newSwitch box((213/512:ℝ),(427/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1108 right_from cover_node_1109

return_split cover_node_1111 edge_at .newSwitch box((213/512:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1107 right_from cover_node_1110

return_split cover_node_1112 edge_at .newSwitch box((425/1024:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (213/512:ℝ) left_from cover_node_1105 right_from cover_node_1111

return_split cover_node_1113 edge_at .newSwitch box((423/1024:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (425/1024:ℝ) left_from cover_node_1099 right_from cover_node_1112

return_split cover_node_1114 edge_at .newSwitch box((419/1024:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (423/1024:ℝ) left_from cover_node_1086 right_from cover_node_1113

return_split cover_node_1115 edge_at .newSwitch box((101/256:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (419/1024:ℝ) left_from cover_node_1059 right_from cover_node_1114

return_split cover_node_1116 edge_at .newSwitch box((0:ℝ),(427/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (101/256:ℝ) left_from cover_node_1004 right_from cover_node_1115

return_split cover_node_1117 edge_at .newSwitch box((427/1024:ℝ),(107/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1121 right_from envelope_row1122

return_split cover_node_1118 edge_at .newSwitch box((427/1024:ℝ),(107/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1120 right_from cover_node_1117

return_split cover_node_1119 edge_at .newSwitch box((427/1024:ℝ),(107/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1123 right_from envelope_row1124

return_split cover_node_1120 edge_at .newSwitch box((427/1024:ℝ),(107/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1125 right_from envelope_row1126

return_split cover_node_1121 edge_at .newSwitch box((427/1024:ℝ),(107/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1119 right_from cover_node_1120

return_split cover_node_1122 edge_at .newSwitch box((427/1024:ℝ),(107/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1118 right_from cover_node_1121

return_split cover_node_1123 edge_at .newSwitch box((107/256:ℝ),(429/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1128 right_from envelope_row1129

return_split cover_node_1124 edge_at .newSwitch box((107/256:ℝ),(429/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1127 right_from cover_node_1123

return_split cover_node_1125 edge_at .newSwitch box((107/256:ℝ),(429/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1130 right_from envelope_row1131

return_split cover_node_1126 edge_at .newSwitch box((107/256:ℝ),(429/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1132 right_from envelope_row1133

return_split cover_node_1127 edge_at .newSwitch box((107/256:ℝ),(429/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1125 right_from cover_node_1126

return_split cover_node_1128 edge_at .newSwitch box((107/256:ℝ),(429/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1124 right_from cover_node_1127

return_split cover_node_1129 edge_at .newSwitch box((427/1024:ℝ),(429/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (107/256:ℝ) left_from cover_node_1122 right_from cover_node_1128

return_split cover_node_1130 edge_at .newSwitch box((429/1024:ℝ),(215/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1135 right_from envelope_row1136

return_split cover_node_1131 edge_at .newSwitch box((429/1024:ℝ),(215/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1134 right_from cover_node_1130

return_split cover_node_1132 edge_at .newSwitch box((429/1024:ℝ),(215/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1137 right_from envelope_row1138

return_split cover_node_1133 edge_at .newSwitch box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1139 right_from envelope_row1140

return_split cover_node_1134 edge_at .newSwitch box((429/1024:ℝ),(215/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1132 right_from cover_node_1133

return_split cover_node_1135 edge_at .newSwitch box((429/1024:ℝ),(215/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1131 right_from cover_node_1134

return_split cover_node_1136 edge_at .newSwitch box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1142 right_from envelope_row1143

return_split cover_node_1137 edge_at .newSwitch box((215/512:ℝ),(431/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1141 right_from cover_node_1136

return_split cover_node_1138 edge_at .newSwitch box((215/512:ℝ),(431/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1144 right_from envelope_row1145

return_split cover_node_1139 edge_at .newSwitch box((215/512:ℝ),(431/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1146 right_from envelope_row1147

return_split cover_node_1140 edge_at .newSwitch box((215/512:ℝ),(431/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1138 right_from cover_node_1139

return_split cover_node_1141 edge_at .newSwitch box((215/512:ℝ),(431/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1137 right_from cover_node_1140

return_split cover_node_1142 edge_at .newSwitch box((429/1024:ℝ),(431/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (215/512:ℝ) left_from cover_node_1135 right_from cover_node_1141

return_split cover_node_1143 edge_at .newSwitch box((427/1024:ℝ),(431/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (429/1024:ℝ) left_from cover_node_1129 right_from cover_node_1142

return_split cover_node_1144 edge_at .newSwitch box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1149 right_from envelope_row1150

return_split cover_node_1145 edge_at .newSwitch box((431/1024:ℝ),(27/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1148 right_from cover_node_1144

return_split cover_node_1146 edge_at .newSwitch box((431/1024:ℝ),(27/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1151 right_from envelope_row1152

return_split cover_node_1147 edge_at .newSwitch box((431/1024:ℝ),(27/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1153 right_from envelope_row1154

return_split cover_node_1148 edge_at .newSwitch box((431/1024:ℝ),(27/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1146 right_from cover_node_1147

return_split cover_node_1149 edge_at .newSwitch box((431/1024:ℝ),(27/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1145 right_from cover_node_1148

return_split cover_node_1150 edge_at .newSwitch box((27/64:ℝ),(433/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1156 right_from envelope_row1157

return_split cover_node_1151 edge_at .newSwitch box((27/64:ℝ),(433/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1155 right_from cover_node_1150

return_split cover_node_1152 edge_at .newSwitch box((27/64:ℝ),(433/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1158 right_from envelope_row1159

return_split cover_node_1153 edge_at .newSwitch box((27/64:ℝ),(433/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1160 right_from envelope_row1161

return_split cover_node_1154 edge_at .newSwitch box((27/64:ℝ),(433/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1152 right_from cover_node_1153

return_split cover_node_1155 edge_at .newSwitch box((27/64:ℝ),(433/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1151 right_from cover_node_1154

return_split cover_node_1156 edge_at .newSwitch box((431/1024:ℝ),(433/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (27/64:ℝ) left_from cover_node_1149 right_from cover_node_1155

return_split cover_node_1157 edge_at .newSwitch box((433/1024:ℝ),(217/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1163 right_from envelope_row1164

return_split cover_node_1158 edge_at .newSwitch box((433/1024:ℝ),(217/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1162 right_from cover_node_1157

return_split cover_node_1159 edge_at .newSwitch box((433/1024:ℝ),(217/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1165 right_from envelope_row1166

return_split cover_node_1160 edge_at .newSwitch box((433/1024:ℝ),(217/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1167 right_from envelope_row1168

return_split cover_node_1161 edge_at .newSwitch box((433/1024:ℝ),(217/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1159 right_from cover_node_1160

return_split cover_node_1162 edge_at .newSwitch box((433/1024:ℝ),(217/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1158 right_from cover_node_1161

return_split cover_node_1163 edge_at .newSwitch box((217/512:ℝ),(435/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1170 right_from envelope_row1171

return_split cover_node_1164 edge_at .newSwitch box((217/512:ℝ),(435/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1169 right_from cover_node_1163

return_split cover_node_1165 edge_at .newSwitch box((217/512:ℝ),(435/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1172 right_from envelope_row1173

return_split cover_node_1166 edge_at .newSwitch box((217/512:ℝ),(435/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1174 right_from envelope_row1175

return_split cover_node_1167 edge_at .newSwitch box((217/512:ℝ),(435/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1165 right_from cover_node_1166

return_split cover_node_1168 edge_at .newSwitch box((217/512:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1164 right_from cover_node_1167

return_split cover_node_1169 edge_at .newSwitch box((433/1024:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (217/512:ℝ) left_from cover_node_1162 right_from cover_node_1168

return_split cover_node_1170 edge_at .newSwitch box((431/1024:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (433/1024:ℝ) left_from cover_node_1156 right_from cover_node_1169

return_split cover_node_1171 edge_at .newSwitch box((427/1024:ℝ),(435/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (431/1024:ℝ) left_from cover_node_1143 right_from cover_node_1170

return_split cover_node_1172 edge_at .newSwitch box((435/1024:ℝ),(109/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1177 right_from envelope_row1178

return_split cover_node_1173 edge_at .newSwitch box((435/1024:ℝ),(109/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1176 right_from cover_node_1172

return_split cover_node_1174 edge_at .newSwitch box((435/1024:ℝ),(109/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1179 right_from envelope_row1180

return_split cover_node_1175 edge_at .newSwitch box((435/1024:ℝ),(109/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1181 right_from envelope_row1182

return_split cover_node_1176 edge_at .newSwitch box((435/1024:ℝ),(109/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1174 right_from cover_node_1175

return_split cover_node_1177 edge_at .newSwitch box((435/1024:ℝ),(109/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1173 right_from cover_node_1176

return_split cover_node_1178 edge_at .newSwitch box((109/256:ℝ),(437/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1184 right_from envelope_row1185

return_split cover_node_1179 edge_at .newSwitch box((109/256:ℝ),(437/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1183 right_from cover_node_1178

return_split cover_node_1180 edge_at .newSwitch box((109/256:ℝ),(437/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1186 right_from envelope_row1187

return_split cover_node_1181 edge_at .newSwitch box((109/256:ℝ),(437/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1188 right_from envelope_row1189

return_split cover_node_1182 edge_at .newSwitch box((109/256:ℝ),(437/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1180 right_from cover_node_1181

return_split cover_node_1183 edge_at .newSwitch box((109/256:ℝ),(437/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1179 right_from cover_node_1182

return_split cover_node_1184 edge_at .newSwitch box((435/1024:ℝ),(437/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (109/256:ℝ) left_from cover_node_1177 right_from cover_node_1183

return_split cover_node_1185 edge_at .newSwitch box((437/1024:ℝ),(219/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1191 right_from envelope_row1192

return_split cover_node_1186 edge_at .newSwitch box((437/1024:ℝ),(219/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1190 right_from cover_node_1185

return_split cover_node_1187 edge_at .newSwitch box((437/1024:ℝ),(219/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1193 right_from envelope_row1194

return_split cover_node_1188 edge_at .newSwitch box((437/1024:ℝ),(219/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1195 right_from envelope_row1196

return_split cover_node_1189 edge_at .newSwitch box((437/1024:ℝ),(219/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1187 right_from cover_node_1188

return_split cover_node_1190 edge_at .newSwitch box((437/1024:ℝ),(219/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1186 right_from cover_node_1189

return_split cover_node_1191 edge_at .newSwitch box((219/512:ℝ),(439/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1198 right_from envelope_row1199

return_split cover_node_1192 edge_at .newSwitch box((219/512:ℝ),(439/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1197 right_from cover_node_1191

return_split cover_node_1193 edge_at .newSwitch box((219/512:ℝ),(439/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1200 right_from envelope_row1201

return_split cover_node_1194 edge_at .newSwitch box((219/512:ℝ),(439/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1202 right_from envelope_row1203

return_split cover_node_1195 edge_at .newSwitch box((219/512:ℝ),(439/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1193 right_from cover_node_1194

return_split cover_node_1196 edge_at .newSwitch box((219/512:ℝ),(439/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1192 right_from cover_node_1195

return_split cover_node_1197 edge_at .newSwitch box((437/1024:ℝ),(439/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (219/512:ℝ) left_from cover_node_1190 right_from cover_node_1196

return_split cover_node_1198 edge_at .newSwitch box((435/1024:ℝ),(439/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (437/1024:ℝ) left_from cover_node_1184 right_from cover_node_1197

return_split cover_node_1199 edge_at .newSwitch box((439/1024:ℝ),(55/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1205 right_from envelope_row1206

return_split cover_node_1200 edge_at .newSwitch box((439/1024:ℝ),(55/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1204 right_from cover_node_1199

return_split cover_node_1201 edge_at .newSwitch box((439/1024:ℝ),(55/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1207 right_from envelope_row1208

return_split cover_node_1202 edge_at .newSwitch box((439/1024:ℝ),(55/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1209 right_from envelope_row1210

return_split cover_node_1203 edge_at .newSwitch box((439/1024:ℝ),(55/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1201 right_from cover_node_1202

return_split cover_node_1204 edge_at .newSwitch box((439/1024:ℝ),(55/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1200 right_from cover_node_1203

return_split cover_node_1205 edge_at .newSwitch box((55/128:ℝ),(111/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1212 right_from envelope_row1213

return_split cover_node_1206 edge_at .newSwitch box((55/128:ℝ),(111/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1211 right_from cover_node_1205

return_split cover_node_1207 edge_at .newSwitch box((55/128:ℝ),(111/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1214 right_from envelope_row1215

return_split cover_node_1208 edge_at .newSwitch box((55/128:ℝ),(111/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1216 right_from envelope_row1217

return_split cover_node_1209 edge_at .newSwitch box((55/128:ℝ),(111/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1207 right_from cover_node_1208

return_split cover_node_1210 edge_at .newSwitch box((55/128:ℝ),(111/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1206 right_from cover_node_1209

return_split cover_node_1211 edge_at .newSwitch box((439/1024:ℝ),(111/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (55/128:ℝ) left_from cover_node_1204 right_from cover_node_1210

return_split cover_node_1212 edge_at .newSwitch box((111/256:ℝ),(7/16:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1219 right_from envelope_row1220

return_split cover_node_1213 edge_at .newSwitch box((111/256:ℝ),(7/16:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1218 right_from cover_node_1212

return_split cover_node_1214 edge_at .newSwitch box((111/256:ℝ),(7/16:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1221 right_from envelope_row1222

return_split cover_node_1215 edge_at .newSwitch box((111/256:ℝ),(7/16:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1223 right_from envelope_row1224

return_split cover_node_1216 edge_at .newSwitch box((111/256:ℝ),(7/16:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1214 right_from cover_node_1215

return_split cover_node_1217 edge_at .newSwitch box((111/256:ℝ),(7/16:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1213 right_from cover_node_1216

return_split cover_node_1218 edge_at .newSwitch box((7/16:ℝ),(225/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1226 right_from envelope_row1227

return_split cover_node_1219 edge_at .newSwitch box((7/16:ℝ),(225/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1225 right_from cover_node_1218

return_split cover_node_1220 edge_at .newSwitch box((7/16:ℝ),(225/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1228 right_from envelope_row1229

return_split cover_node_1221 edge_at .newSwitch box((7/16:ℝ),(225/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1230 right_from envelope_row1231

return_split cover_node_1222 edge_at .newSwitch box((7/16:ℝ),(225/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1220 right_from cover_node_1221

return_split cover_node_1223 edge_at .newSwitch box((7/16:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1219 right_from cover_node_1222

return_split cover_node_1224 edge_at .newSwitch box((111/256:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (7/16:ℝ) left_from cover_node_1217 right_from cover_node_1223

return_split cover_node_1225 edge_at .newSwitch box((439/1024:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (111/256:ℝ) left_from cover_node_1211 right_from cover_node_1224

return_split cover_node_1226 edge_at .newSwitch box((435/1024:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (439/1024:ℝ) left_from cover_node_1198 right_from cover_node_1225

return_split cover_node_1227 edge_at .newSwitch box((427/1024:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (435/1024:ℝ) left_from cover_node_1171 right_from cover_node_1226

return_split cover_node_1228 edge_at .newSwitch box((225/512:ℝ),(453/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1233 right_from envelope_row1234

return_split cover_node_1229 edge_at .newSwitch box((225/512:ℝ),(453/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1232 right_from cover_node_1228

return_split cover_node_1230 edge_at .newSwitch box((225/512:ℝ),(453/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1235 right_from envelope_row1236

return_split cover_node_1231 edge_at .newSwitch box((225/512:ℝ),(453/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1237 right_from envelope_row1238

return_split cover_node_1232 edge_at .newSwitch box((225/512:ℝ),(453/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1230 right_from cover_node_1231

return_split cover_node_1233 edge_at .newSwitch box((225/512:ℝ),(453/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1229 right_from cover_node_1232

return_split cover_node_1234 edge_at .newSwitch box((453/1024:ℝ),(57/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1240 right_from envelope_row1241

return_split cover_node_1235 edge_at .newSwitch box((453/1024:ℝ),(57/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1239 right_from cover_node_1234

return_split cover_node_1236 edge_at .newSwitch box((453/1024:ℝ),(57/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1242 right_from envelope_row1243

return_split cover_node_1237 edge_at .newSwitch box((453/1024:ℝ),(57/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1244 right_from envelope_row1245

return_split cover_node_1238 edge_at .newSwitch box((453/1024:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1236 right_from cover_node_1237

return_split cover_node_1239 edge_at .newSwitch box((453/1024:ℝ),(57/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1235 right_from cover_node_1238

return_split cover_node_1240 edge_at .newSwitch box((225/512:ℝ),(57/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (453/1024:ℝ) left_from cover_node_1233 right_from cover_node_1239

return_split cover_node_1241 edge_at .newSwitch box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1247 right_from envelope_row1248

return_split cover_node_1242 edge_at .newSwitch box((57/128:ℝ),(29/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1246 right_from cover_node_1241

return_split cover_node_1243 edge_at .newSwitch box((57/128:ℝ),(29/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1249 right_from envelope_row1250

return_split cover_node_1244 edge_at .newSwitch box((57/128:ℝ),(29/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1251 right_from envelope_row1252

return_split cover_node_1245 edge_at .newSwitch box((57/128:ℝ),(29/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1243 right_from cover_node_1244

return_split cover_node_1246 edge_at .newSwitch box((57/128:ℝ),(29/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1242 right_from cover_node_1245

return_split cover_node_1247 edge_at .newSwitch box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1254 right_from envelope_row1255

return_split cover_node_1248 edge_at .newSwitch box((29/64:ℝ),(59/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1253 right_from cover_node_1247

return_split cover_node_1249 edge_at .newSwitch box((29/64:ℝ),(59/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1256 right_from envelope_row1257

return_split cover_node_1250 edge_at .newSwitch box((29/64:ℝ),(59/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1258 right_from envelope_row1259

return_split cover_node_1251 edge_at .newSwitch box((29/64:ℝ),(59/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1249 right_from cover_node_1250

return_split cover_node_1252 edge_at .newSwitch box((29/64:ℝ),(59/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1248 right_from cover_node_1251

return_split cover_node_1253 edge_at .newSwitch box((57/128:ℝ),(59/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (29/64:ℝ) left_from cover_node_1246 right_from cover_node_1252

return_split cover_node_1254 edge_at .newSwitch box((225/512:ℝ),(59/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (57/128:ℝ) left_from cover_node_1240 right_from cover_node_1253

return_split cover_node_1255 edge_at .newSwitch box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1261 right_from envelope_row1262

return_split cover_node_1256 edge_at .newSwitch box((59/128:ℝ),(15/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1260 right_from cover_node_1255

return_split cover_node_1257 edge_at .newSwitch box((59/128:ℝ),(15/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1263 right_from envelope_row1264

return_split cover_node_1258 edge_at .newSwitch box((59/128:ℝ),(15/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1265 right_from envelope_row1266

return_split cover_node_1259 edge_at .newSwitch box((59/128:ℝ),(15/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1257 right_from cover_node_1258

return_split cover_node_1260 edge_at .newSwitch box((59/128:ℝ),(15/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1256 right_from cover_node_1259

return_split cover_node_1261 edge_at .newSwitch box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1268 right_from envelope_row1269

return_split cover_node_1262 edge_at .newSwitch box((15/32:ℝ),(61/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1267 right_from cover_node_1261

return_split cover_node_1263 edge_at .newSwitch box((15/32:ℝ),(61/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1270 right_from envelope_row1271

return_split cover_node_1264 edge_at .newSwitch box((15/32:ℝ),(61/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1272 right_from envelope_row1273

return_split cover_node_1265 edge_at .newSwitch box((15/32:ℝ),(61/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1263 right_from cover_node_1264

return_split cover_node_1266 edge_at .newSwitch box((15/32:ℝ),(61/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1262 right_from cover_node_1265

return_split cover_node_1267 edge_at .newSwitch box((59/128:ℝ),(61/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (15/32:ℝ) left_from cover_node_1260 right_from cover_node_1266

return_split cover_node_1268 edge_at .newSwitch box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1275 right_from envelope_row1276

return_split cover_node_1269 edge_at .newSwitch box((61/128:ℝ),(31/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1274 right_from cover_node_1268

return_split cover_node_1270 edge_at .newSwitch box((61/128:ℝ),(31/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1277 right_from envelope_row1278

return_split cover_node_1271 edge_at .newSwitch box((61/128:ℝ),(31/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1279 right_from envelope_row1280

return_split cover_node_1272 edge_at .newSwitch box((61/128:ℝ),(31/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1270 right_from cover_node_1271

return_split cover_node_1273 edge_at .newSwitch box((61/128:ℝ),(31/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1269 right_from cover_node_1272

return_split cover_node_1274 edge_at .newSwitch box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1282 right_from envelope_row1283

return_split cover_node_1275 edge_at .newSwitch box((31/64:ℝ),(63/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1281 right_from cover_node_1274

return_split cover_node_1276 edge_at .newSwitch box((31/64:ℝ),(63/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1284 right_from envelope_row1285

return_split cover_node_1277 edge_at .newSwitch box((31/64:ℝ),(63/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1286 right_from envelope_row1287

return_split cover_node_1278 edge_at .newSwitch box((31/64:ℝ),(63/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1276 right_from cover_node_1277

return_split cover_node_1279 edge_at .newSwitch box((31/64:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1275 right_from cover_node_1278

return_split cover_node_1280 edge_at .newSwitch box((61/128:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (31/64:ℝ) left_from cover_node_1273 right_from cover_node_1279

return_split cover_node_1281 edge_at .newSwitch box((59/128:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (61/128:ℝ) left_from cover_node_1267 right_from cover_node_1280

return_split cover_node_1282 edge_at .newSwitch box((225/512:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (59/128:ℝ) left_from cover_node_1254 right_from cover_node_1281

return_split cover_node_1283 edge_at .newSwitch box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1289 right_from envelope_row1290

return_split cover_node_1284 edge_at .newSwitch box((63/128:ℝ),(1/2:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1288 right_from cover_node_1283

return_split cover_node_1285 edge_at .newSwitch box((63/128:ℝ),(1/2:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1291 right_from envelope_row1292

return_split cover_node_1286 edge_at .newSwitch box((63/128:ℝ),(1/2:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1293 right_from envelope_row1294

return_split cover_node_1287 edge_at .newSwitch box((63/128:ℝ),(1/2:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1285 right_from cover_node_1286

return_split cover_node_1288 edge_at .newSwitch box((63/128:ℝ),(1/2:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1284 right_from cover_node_1287

return_split cover_node_1289 edge_at .newSwitch box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1296 right_from envelope_row1297

return_split cover_node_1290 edge_at .newSwitch box((1/2:ℝ),(65/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1295 right_from cover_node_1289

return_split cover_node_1291 edge_at .newSwitch box((1/2:ℝ),(65/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1298 right_from envelope_row1299

return_split cover_node_1292 edge_at .newSwitch box((1/2:ℝ),(65/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1300 right_from envelope_row1301

return_split cover_node_1293 edge_at .newSwitch box((1/2:ℝ),(65/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1291 right_from cover_node_1292

return_split cover_node_1294 edge_at .newSwitch box((1/2:ℝ),(65/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1290 right_from cover_node_1293

return_split cover_node_1295 edge_at .newSwitch box((63/128:ℝ),(65/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (1/2:ℝ) left_from cover_node_1288 right_from cover_node_1294

return_split cover_node_1296 edge_at .newSwitch box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1303 right_from envelope_row1304

return_split cover_node_1297 edge_at .newSwitch box((65/128:ℝ),(33/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1302 right_from cover_node_1296

return_split cover_node_1298 edge_at .newSwitch box((65/128:ℝ),(33/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1305 right_from envelope_row1306

return_split cover_node_1299 edge_at .newSwitch box((65/128:ℝ),(33/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1307 right_from envelope_row1308

return_split cover_node_1300 edge_at .newSwitch box((65/128:ℝ),(33/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1298 right_from cover_node_1299

return_split cover_node_1301 edge_at .newSwitch box((65/128:ℝ),(33/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1297 right_from cover_node_1300

return_split cover_node_1302 edge_at .newSwitch box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1310 right_from envelope_row1311

return_split cover_node_1303 edge_at .newSwitch box((33/64:ℝ),(67/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1309 right_from cover_node_1302

return_split cover_node_1304 edge_at .newSwitch box((33/64:ℝ),(67/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1312 right_from envelope_row1313

return_split cover_node_1305 edge_at .newSwitch box((33/64:ℝ),(67/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1314 right_from envelope_row1315

return_split cover_node_1306 edge_at .newSwitch box((33/64:ℝ),(67/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1304 right_from cover_node_1305

return_split cover_node_1307 edge_at .newSwitch box((33/64:ℝ),(67/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1303 right_from cover_node_1306

return_split cover_node_1308 edge_at .newSwitch box((65/128:ℝ),(67/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (33/64:ℝ) left_from cover_node_1301 right_from cover_node_1307

return_split cover_node_1309 edge_at .newSwitch box((63/128:ℝ),(67/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (65/128:ℝ) left_from cover_node_1295 right_from cover_node_1308

return_split cover_node_1310 edge_at .newSwitch box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1317 right_from envelope_row1318

return_split cover_node_1311 edge_at .newSwitch box((67/128:ℝ),(17/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1316 right_from cover_node_1310

return_split cover_node_1312 edge_at .newSwitch box((67/128:ℝ),(17/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1319 right_from envelope_row1320

return_split cover_node_1313 edge_at .newSwitch box((67/128:ℝ),(17/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1321 right_from envelope_row1322

return_split cover_node_1314 edge_at .newSwitch box((67/128:ℝ),(17/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1312 right_from cover_node_1313

return_split cover_node_1315 edge_at .newSwitch box((67/128:ℝ),(17/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1311 right_from cover_node_1314

return_split cover_node_1316 edge_at .newSwitch box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1324 right_from envelope_row1325

return_split cover_node_1317 edge_at .newSwitch box((17/32:ℝ),(69/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1323 right_from cover_node_1316

return_split cover_node_1318 edge_at .newSwitch box((17/32:ℝ),(69/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1326 right_from envelope_row1327

return_split cover_node_1319 edge_at .newSwitch box((17/32:ℝ),(69/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1328 right_from envelope_row1329

return_split cover_node_1320 edge_at .newSwitch box((17/32:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1318 right_from cover_node_1319

return_split cover_node_1321 edge_at .newSwitch box((17/32:ℝ),(69/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1317 right_from cover_node_1320

return_split cover_node_1322 edge_at .newSwitch box((67/128:ℝ),(69/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (17/32:ℝ) left_from cover_node_1315 right_from cover_node_1321

return_split cover_node_1323 edge_at .newSwitch box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1331 right_from envelope_row1332

return_split cover_node_1324 edge_at .newSwitch box((69/128:ℝ),(35/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1330 right_from cover_node_1323

return_split cover_node_1325 edge_at .newSwitch box((69/128:ℝ),(35/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1333 right_from envelope_row1334

return_split cover_node_1326 edge_at .newSwitch box((69/128:ℝ),(35/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1335 right_from envelope_row1336

return_split cover_node_1327 edge_at .newSwitch box((69/128:ℝ),(35/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1325 right_from cover_node_1326

return_split cover_node_1328 edge_at .newSwitch box((69/128:ℝ),(35/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1324 right_from cover_node_1327

return_split cover_node_1329 edge_at .newSwitch box((35/64:ℝ),(3/4:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1338 right_from envelope_row1339

return_split cover_node_1330 edge_at .newSwitch box((35/64:ℝ),(3/4:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1337 right_from cover_node_1329

return_split cover_node_1331 edge_at .newSwitch box((35/64:ℝ),(3/4:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1340 right_from envelope_row1341

return_split cover_node_1332 edge_at .newSwitch box((35/64:ℝ),(3/4:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1342 right_from envelope_row1343

return_split cover_node_1333 edge_at .newSwitch box((35/64:ℝ),(3/4:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1331 right_from cover_node_1332

return_split cover_node_1334 edge_at .newSwitch box((35/64:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1330 right_from cover_node_1333

return_split cover_node_1335 edge_at .newSwitch box((69/128:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (35/64:ℝ) left_from cover_node_1328 right_from cover_node_1334

return_split cover_node_1336 edge_at .newSwitch box((67/128:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (69/128:ℝ) left_from cover_node_1322 right_from cover_node_1335

return_split cover_node_1337 edge_at .newSwitch box((63/128:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (67/128:ℝ) left_from cover_node_1309 right_from cover_node_1336

return_split cover_node_1338 edge_at .newSwitch box((225/512:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (63/128:ℝ) left_from cover_node_1282 right_from cover_node_1337

return_split cover_node_1339 edge_at .newSwitch box((427/1024:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (225/512:ℝ) left_from cover_node_1227 right_from cover_node_1338

return_split cover_node_1340 edge_at .newSwitch box((0:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (427/1024:ℝ) left_from cover_node_1116 right_from cover_node_1339

return_split cover_node_1341 edge_at .newTop box((0:ℝ),(9/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1345 right_from envelope_row1346

return_split cover_node_1342 edge_at .newTop box((0:ℝ),(9/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1344 right_from cover_node_1341

return_split cover_node_1343 edge_at .newTop box((0:ℝ),(9/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1347 right_from envelope_row1348

return_split cover_node_1344 edge_at .newTop box((0:ℝ),(9/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1349 right_from envelope_row1350

return_split cover_node_1345 edge_at .newTop box((0:ℝ),(9/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1343 right_from cover_node_1344

return_split cover_node_1346 edge_at .newTop box((0:ℝ),(9/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1342 right_from cover_node_1345

return_split cover_node_1347 edge_at .newTop box((9/32:ℝ),(5/16:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1352 right_from envelope_row1353

return_split cover_node_1348 edge_at .newTop box((9/32:ℝ),(5/16:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1351 right_from cover_node_1347

return_split cover_node_1349 edge_at .newTop box((9/32:ℝ),(5/16:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1354 right_from envelope_row1355

return_split cover_node_1350 edge_at .newTop box((9/32:ℝ),(5/16:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1356 right_from envelope_row1357

return_split cover_node_1351 edge_at .newTop box((9/32:ℝ),(5/16:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1349 right_from cover_node_1350

return_split cover_node_1352 edge_at .newTop box((9/32:ℝ),(5/16:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1348 right_from cover_node_1351

return_split cover_node_1353 edge_at .newTop box((0:ℝ),(5/16:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (9/32:ℝ) left_from cover_node_1346 right_from cover_node_1352

return_split cover_node_1354 edge_at .newTop box((5/16:ℝ),(41/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1359 right_from envelope_row1360

return_split cover_node_1355 edge_at .newTop box((5/16:ℝ),(41/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1358 right_from cover_node_1354

return_split cover_node_1356 edge_at .newTop box((5/16:ℝ),(41/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1361 right_from envelope_row1362

return_split cover_node_1357 edge_at .newTop box((5/16:ℝ),(41/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1363 right_from envelope_row1364

return_split cover_node_1358 edge_at .newTop box((5/16:ℝ),(41/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1356 right_from cover_node_1357

return_split cover_node_1359 edge_at .newTop box((5/16:ℝ),(41/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1355 right_from cover_node_1358

return_split cover_node_1360 edge_at .newTop box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1366 right_from envelope_row1367

return_split cover_node_1361 edge_at .newTop box((41/128:ℝ),(21/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1365 right_from cover_node_1360

return_split cover_node_1362 edge_at .newTop box((41/128:ℝ),(21/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1368 right_from envelope_row1369

return_split cover_node_1363 edge_at .newTop box((41/128:ℝ),(21/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1370 right_from envelope_row1371

return_split cover_node_1364 edge_at .newTop box((41/128:ℝ),(21/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1362 right_from cover_node_1363

return_split cover_node_1365 edge_at .newTop box((41/128:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1361 right_from cover_node_1364

return_split cover_node_1366 edge_at .newTop box((5/16:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (41/128:ℝ) left_from cover_node_1359 right_from cover_node_1365

return_split cover_node_1367 edge_at .newTop box((0:ℝ),(21/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (5/16:ℝ) left_from cover_node_1353 right_from cover_node_1366

return_split cover_node_1368 edge_at .newTop box((21/64:ℝ),(43/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1373 right_from envelope_row1374

return_split cover_node_1369 edge_at .newTop box((21/64:ℝ),(43/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1372 right_from cover_node_1368

return_split cover_node_1370 edge_at .newTop box((21/64:ℝ),(43/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1375 right_from envelope_row1376

return_split cover_node_1371 edge_at .newTop box((21/64:ℝ),(43/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1377 right_from envelope_row1378

return_split cover_node_1372 edge_at .newTop box((21/64:ℝ),(43/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1370 right_from cover_node_1371

return_split cover_node_1373 edge_at .newTop box((21/64:ℝ),(43/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1369 right_from cover_node_1372

return_split cover_node_1374 edge_at .newTop box((43/128:ℝ),(11/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1380 right_from envelope_row1381

return_split cover_node_1375 edge_at .newTop box((43/128:ℝ),(11/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1379 right_from cover_node_1374

return_split cover_node_1376 edge_at .newTop box((43/128:ℝ),(11/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1382 right_from envelope_row1383

return_split cover_node_1377 edge_at .newTop box((43/128:ℝ),(11/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1384 right_from envelope_row1385

return_split cover_node_1378 edge_at .newTop box((43/128:ℝ),(11/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1376 right_from cover_node_1377

return_split cover_node_1379 edge_at .newTop box((43/128:ℝ),(11/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1375 right_from cover_node_1378

return_split cover_node_1380 edge_at .newTop box((21/64:ℝ),(11/32:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (43/128:ℝ) left_from cover_node_1373 right_from cover_node_1379

return_split cover_node_1381 edge_at .newTop box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1387 right_from envelope_row1388

return_split cover_node_1382 edge_at .newTop box((11/32:ℝ),(45/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1386 right_from cover_node_1381

return_split cover_node_1383 edge_at .newTop box((11/32:ℝ),(45/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1389 right_from envelope_row1390

return_split cover_node_1384 edge_at .newTop box((11/32:ℝ),(45/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1391 right_from envelope_row1392

return_split cover_node_1385 edge_at .newTop box((11/32:ℝ),(45/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1383 right_from cover_node_1384

return_split cover_node_1386 edge_at .newTop box((11/32:ℝ),(45/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1382 right_from cover_node_1385

return_split cover_node_1387 edge_at .newTop box((45/128:ℝ),(23/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1394 right_from envelope_row1395

return_split cover_node_1388 edge_at .newTop box((45/128:ℝ),(23/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1393 right_from cover_node_1387

return_split cover_node_1389 edge_at .newTop box((45/128:ℝ),(23/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1396 right_from envelope_row1397

return_split cover_node_1390 edge_at .newTop box((45/128:ℝ),(23/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1398 right_from envelope_row1399

return_split cover_node_1391 edge_at .newTop box((45/128:ℝ),(23/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1389 right_from cover_node_1390

return_split cover_node_1392 edge_at .newTop box((45/128:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1388 right_from cover_node_1391

return_split cover_node_1393 edge_at .newTop box((11/32:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (45/128:ℝ) left_from cover_node_1386 right_from cover_node_1392

return_split cover_node_1394 edge_at .newTop box((21/64:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (11/32:ℝ) left_from cover_node_1380 right_from cover_node_1393

return_split cover_node_1395 edge_at .newTop box((0:ℝ),(23/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (21/64:ℝ) left_from cover_node_1367 right_from cover_node_1394

return_split cover_node_1396 edge_at .newTop box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1401 right_from envelope_row1402

return_split cover_node_1397 edge_at .newTop box((23/64:ℝ),(47/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1400 right_from cover_node_1396

return_split cover_node_1398 edge_at .newTop box((23/64:ℝ),(47/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1403 right_from envelope_row1404

return_split cover_node_1399 edge_at .newTop box((23/64:ℝ),(47/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1405 right_from envelope_row1406

return_split cover_node_1400 edge_at .newTop box((23/64:ℝ),(47/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1398 right_from cover_node_1399

return_split cover_node_1401 edge_at .newTop box((23/64:ℝ),(47/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1397 right_from cover_node_1400

return_split cover_node_1402 edge_at .newTop box((47/128:ℝ),(3/8:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1408 right_from envelope_row1409

return_split cover_node_1403 edge_at .newTop box((47/128:ℝ),(3/8:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1407 right_from cover_node_1402

return_split cover_node_1404 edge_at .newTop box((47/128:ℝ),(3/8:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1410 right_from envelope_row1411

return_split cover_node_1405 edge_at .newTop box((47/128:ℝ),(3/8:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1412 right_from envelope_row1413

return_split cover_node_1406 edge_at .newTop box((47/128:ℝ),(3/8:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1404 right_from cover_node_1405

return_split cover_node_1407 edge_at .newTop box((47/128:ℝ),(3/8:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1403 right_from cover_node_1406

return_split cover_node_1408 edge_at .newTop box((23/64:ℝ),(3/8:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (47/128:ℝ) left_from cover_node_1401 right_from cover_node_1407

return_split cover_node_1409 edge_at .newTop box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1415 right_from envelope_row1416

return_split cover_node_1410 edge_at .newTop box((3/8:ℝ),(49/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1414 right_from cover_node_1409

return_split cover_node_1411 edge_at .newTop box((3/8:ℝ),(49/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1417 right_from envelope_row1418

return_split cover_node_1412 edge_at .newTop box((3/8:ℝ),(49/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1419 right_from envelope_row1420

return_split cover_node_1413 edge_at .newTop box((3/8:ℝ),(49/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1411 right_from cover_node_1412

return_split cover_node_1414 edge_at .newTop box((3/8:ℝ),(49/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1410 right_from cover_node_1413

return_split cover_node_1415 edge_at .newTop box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1422 right_from envelope_row1423

return_split cover_node_1416 edge_at .newTop box((49/128:ℝ),(25/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1421 right_from cover_node_1415

return_split cover_node_1417 edge_at .newTop box((49/128:ℝ),(25/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1424 right_from envelope_row1425

return_split cover_node_1418 edge_at .newTop box((49/128:ℝ),(25/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1426 right_from envelope_row1427

return_split cover_node_1419 edge_at .newTop box((49/128:ℝ),(25/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1417 right_from cover_node_1418

return_split cover_node_1420 edge_at .newTop box((49/128:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1416 right_from cover_node_1419

return_split cover_node_1421 edge_at .newTop box((3/8:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (49/128:ℝ) left_from cover_node_1414 right_from cover_node_1420

return_split cover_node_1422 edge_at .newTop box((23/64:ℝ),(25/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (3/8:ℝ) left_from cover_node_1408 right_from cover_node_1421

return_split cover_node_1423 edge_at .newTop box((25/64:ℝ),(401/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1429 right_from envelope_row1430

return_split cover_node_1424 edge_at .newTop box((25/64:ℝ),(401/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1428 right_from cover_node_1423

return_split cover_node_1425 edge_at .newTop box((401/1024:ℝ),(201/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1436 right_from envelope_row1437

return_split cover_node_1426 edge_at .newTop box((401/1024:ℝ),(201/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1435 right_from cover_node_1425

return_split cover_node_1427 edge_at .newTop box((25/64:ℝ),(201/512:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (401/1024:ℝ) left_from cover_node_1424 right_from cover_node_1426

return_split cover_node_1428 edge_at .newTop box((201/512:ℝ),(403/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1443 right_from envelope_row1444

return_split cover_node_1429 edge_at .newTop box((201/512:ℝ),(403/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1442 right_from cover_node_1428

return_split cover_node_1430 edge_at .newTop box((403/1024:ℝ),(101/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1450 right_from envelope_row1451

return_split cover_node_1431 edge_at .newTop box((403/1024:ℝ),(101/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1449 right_from cover_node_1430

return_split cover_node_1432 edge_at .newTop box((101/256:ℝ),(405/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1457 right_from envelope_row1458

return_split cover_node_1433 edge_at .newTop box((101/256:ℝ),(405/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1456 right_from cover_node_1432

return_split cover_node_1434 edge_at .newTop box((403/1024:ℝ),(405/1024:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (101/256:ℝ) left_from cover_node_1431 right_from cover_node_1433

return_split cover_node_1435 edge_at .newTop box((201/512:ℝ),(405/1024:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (403/1024:ℝ) left_from cover_node_1429 right_from cover_node_1434

return_split cover_node_1436 edge_at .newTop box((25/64:ℝ),(405/1024:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (201/512:ℝ) left_from cover_node_1427 right_from cover_node_1435

return_split cover_node_1437 edge_at .newTop box((25/64:ℝ),(201/512:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (401/1024:ℝ) left_from envelope_row1431 right_from envelope_row1438

return_split cover_node_1438 edge_at .newTop box((403/1024:ℝ),(405/1024:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (101/256:ℝ) left_from envelope_row1452 right_from envelope_row1459

return_split cover_node_1439 edge_at .newTop box((201/512:ℝ),(405/1024:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (403/1024:ℝ) left_from envelope_row1445 right_from cover_node_1438

return_split cover_node_1440 edge_at .newTop box((25/64:ℝ),(405/1024:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (201/512:ℝ) left_from cover_node_1437 right_from cover_node_1439

return_split cover_node_1441 edge_at .newTop box((25/64:ℝ),(201/512:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (401/1024:ℝ) left_from envelope_row1432 right_from envelope_row1439

return_split cover_node_1442 edge_at .newTop box((403/1024:ℝ),(405/1024:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (101/256:ℝ) left_from envelope_row1453 right_from envelope_row1460

return_split cover_node_1443 edge_at .newTop box((201/512:ℝ),(405/1024:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (403/1024:ℝ) left_from envelope_row1446 right_from cover_node_1442

return_split cover_node_1444 edge_at .newTop box((25/64:ℝ),(405/1024:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (201/512:ℝ) left_from cover_node_1441 right_from cover_node_1443

return_split cover_node_1445 edge_at .newTop box((25/64:ℝ),(405/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from cover_node_1440 right_from cover_node_1444

return_split cover_node_1446 edge_at .newTop box((25/64:ℝ),(201/512:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (401/1024:ℝ) left_from envelope_row1433 right_from envelope_row1440

return_split cover_node_1447 edge_at .newTop box((403/1024:ℝ),(405/1024:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (101/256:ℝ) left_from envelope_row1454 right_from envelope_row1461

return_split cover_node_1448 edge_at .newTop box((201/512:ℝ),(405/1024:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (403/1024:ℝ) left_from envelope_row1447 right_from cover_node_1447

return_split cover_node_1449 edge_at .newTop box((25/64:ℝ),(405/1024:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (201/512:ℝ) left_from cover_node_1446 right_from cover_node_1448

return_split cover_node_1450 edge_at .newTop box((25/64:ℝ),(201/512:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (401/1024:ℝ) left_from envelope_row1434 right_from envelope_row1441

return_split cover_node_1451 edge_at .newTop box((403/1024:ℝ),(405/1024:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (101/256:ℝ) left_from envelope_row1455 right_from envelope_row1462

return_split cover_node_1452 edge_at .newTop box((201/512:ℝ),(405/1024:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (403/1024:ℝ) left_from envelope_row1448 right_from cover_node_1451

return_split cover_node_1453 edge_at .newTop box((25/64:ℝ),(405/1024:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (201/512:ℝ) left_from cover_node_1450 right_from cover_node_1452

return_split cover_node_1454 edge_at .newTop box((25/64:ℝ),(405/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from cover_node_1449 right_from cover_node_1453

return_split cover_node_1455 edge_at .newTop box((25/64:ℝ),(405/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1445 right_from cover_node_1454

return_split cover_node_1456 edge_at .newTop box((25/64:ℝ),(405/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1436 right_from cover_node_1455

return_split cover_node_1457 edge_at .newTop box((23/64:ℝ),(405/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (25/64:ℝ) left_from cover_node_1422 right_from cover_node_1456

return_split cover_node_1458 edge_at .newTop box((0:ℝ),(405/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (23/64:ℝ) left_from cover_node_1395 right_from cover_node_1457

return_split cover_node_1459 edge_at .newTop box((405/1024:ℝ),(203/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1464 right_from envelope_row1465

return_split cover_node_1460 edge_at .newTop box((405/1024:ℝ),(203/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1463 right_from cover_node_1459

return_split cover_node_1461 edge_at .newTop box((405/1024:ℝ),(203/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1466 right_from envelope_row1467

return_split cover_node_1462 edge_at .newTop box((405/1024:ℝ),(203/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1468 right_from envelope_row1469

return_split cover_node_1463 edge_at .newTop box((405/1024:ℝ),(203/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1461 right_from cover_node_1462

return_split cover_node_1464 edge_at .newTop box((405/1024:ℝ),(203/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1460 right_from cover_node_1463

return_split cover_node_1465 edge_at .newTop box((203/512:ℝ),(407/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1471 right_from envelope_row1472

return_split cover_node_1466 edge_at .newTop box((203/512:ℝ),(407/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1470 right_from cover_node_1465

return_split cover_node_1467 edge_at .newTop box((203/512:ℝ),(407/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1473 right_from envelope_row1474

return_split cover_node_1468 edge_at .newTop box((203/512:ℝ),(407/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1475 right_from envelope_row1476

return_split cover_node_1469 edge_at .newTop box((203/512:ℝ),(407/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1467 right_from cover_node_1468

return_split cover_node_1470 edge_at .newTop box((203/512:ℝ),(407/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1466 right_from cover_node_1469

return_split cover_node_1471 edge_at .newTop box((405/1024:ℝ),(407/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (203/512:ℝ) left_from cover_node_1464 right_from cover_node_1470

return_split cover_node_1472 edge_at .newTop box((407/1024:ℝ),(51/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1478 right_from envelope_row1479

return_split cover_node_1473 edge_at .newTop box((407/1024:ℝ),(51/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1477 right_from cover_node_1472

return_split cover_node_1474 edge_at .newTop box((407/1024:ℝ),(51/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1480 right_from envelope_row1481

return_split cover_node_1475 edge_at .newTop box((407/1024:ℝ),(51/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1482 right_from envelope_row1483

return_split cover_node_1476 edge_at .newTop box((407/1024:ℝ),(51/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1474 right_from cover_node_1475

return_split cover_node_1477 edge_at .newTop box((407/1024:ℝ),(51/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1473 right_from cover_node_1476

return_split cover_node_1478 edge_at .newTop box((51/128:ℝ),(13/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1485 right_from envelope_row1486

return_split cover_node_1479 edge_at .newTop box((51/128:ℝ),(13/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1484 right_from cover_node_1478

return_split cover_node_1480 edge_at .newTop box((51/128:ℝ),(13/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1487 right_from envelope_row1488

return_split cover_node_1481 edge_at .newTop box((51/128:ℝ),(13/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1489 right_from envelope_row1490

return_split cover_node_1482 edge_at .newTop box((51/128:ℝ),(13/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1480 right_from cover_node_1481

return_split cover_node_1483 edge_at .newTop box((51/128:ℝ),(13/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1479 right_from cover_node_1482

return_split cover_node_1484 edge_at .newTop box((407/1024:ℝ),(13/32:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (51/128:ℝ) left_from cover_node_1477 right_from cover_node_1483

return_split cover_node_1485 edge_at .newTop box((405/1024:ℝ),(13/32:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (407/1024:ℝ) left_from cover_node_1471 right_from cover_node_1484

return_split cover_node_1486 edge_at .newTop box((13/32:ℝ),(417/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1492 right_from envelope_row1493

return_split cover_node_1487 edge_at .newTop box((13/32:ℝ),(417/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1491 right_from cover_node_1486

return_split cover_node_1488 edge_at .newTop box((13/32:ℝ),(417/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1494 right_from envelope_row1495

return_split cover_node_1489 edge_at .newTop box((13/32:ℝ),(417/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1496 right_from envelope_row1497

return_split cover_node_1490 edge_at .newTop box((13/32:ℝ),(417/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1488 right_from cover_node_1489

return_split cover_node_1491 edge_at .newTop box((13/32:ℝ),(417/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1487 right_from cover_node_1490

return_split cover_node_1492 edge_at .newTop box((417/1024:ℝ),(209/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1499 right_from envelope_row1500

return_split cover_node_1493 edge_at .newTop box((417/1024:ℝ),(209/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1498 right_from cover_node_1492

return_split cover_node_1494 edge_at .newTop box((417/1024:ℝ),(209/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1501 right_from envelope_row1502

return_split cover_node_1495 edge_at .newTop box((417/1024:ℝ),(209/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1503 right_from envelope_row1504

return_split cover_node_1496 edge_at .newTop box((417/1024:ℝ),(209/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1494 right_from cover_node_1495

return_split cover_node_1497 edge_at .newTop box((417/1024:ℝ),(209/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1493 right_from cover_node_1496

return_split cover_node_1498 edge_at .newTop box((13/32:ℝ),(209/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (417/1024:ℝ) left_from cover_node_1491 right_from cover_node_1497

return_split cover_node_1499 edge_at .newTop box((209/512:ℝ),(419/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1506 right_from envelope_row1507

return_split cover_node_1500 edge_at .newTop box((209/512:ℝ),(419/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1505 right_from cover_node_1499

return_split cover_node_1501 edge_at .newTop box((209/512:ℝ),(419/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1508 right_from envelope_row1509

return_split cover_node_1502 edge_at .newTop box((209/512:ℝ),(419/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1510 right_from envelope_row1511

return_split cover_node_1503 edge_at .newTop box((209/512:ℝ),(419/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1501 right_from cover_node_1502

return_split cover_node_1504 edge_at .newTop box((209/512:ℝ),(419/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1500 right_from cover_node_1503

return_split cover_node_1505 edge_at .newTop box((419/1024:ℝ),(105/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1513 right_from envelope_row1514

return_split cover_node_1506 edge_at .newTop box((419/1024:ℝ),(105/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1512 right_from cover_node_1505

return_split cover_node_1507 edge_at .newTop box((419/1024:ℝ),(105/256:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1515 right_from envelope_row1516

return_split cover_node_1508 edge_at .newTop box((419/1024:ℝ),(105/256:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1517 right_from envelope_row1518

return_split cover_node_1509 edge_at .newTop box((419/1024:ℝ),(105/256:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1507 right_from cover_node_1508

return_split cover_node_1510 edge_at .newTop box((419/1024:ℝ),(105/256:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1506 right_from cover_node_1509

return_split cover_node_1511 edge_at .newTop box((209/512:ℝ),(105/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (419/1024:ℝ) left_from cover_node_1504 right_from cover_node_1510

return_split cover_node_1512 edge_at .newTop box((13/32:ℝ),(105/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (209/512:ℝ) left_from cover_node_1498 right_from cover_node_1511

return_split cover_node_1513 edge_at .newTop box((405/1024:ℝ),(105/256:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (13/32:ℝ) left_from cover_node_1485 right_from cover_node_1512

return_split cover_node_1514 edge_at .newTop box((105/256:ℝ),(421/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1520 right_from envelope_row1521

return_split cover_node_1515 edge_at .newTop box((105/256:ℝ),(421/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1519 right_from cover_node_1514

return_split cover_node_1516 edge_at .newTop box((105/256:ℝ),(421/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1522 right_from envelope_row1523

return_split cover_node_1517 edge_at .newTop box((105/256:ℝ),(421/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1524 right_from envelope_row1525

return_split cover_node_1518 edge_at .newTop box((105/256:ℝ),(421/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1516 right_from cover_node_1517

return_split cover_node_1519 edge_at .newTop box((105/256:ℝ),(421/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1515 right_from cover_node_1518

return_split cover_node_1520 edge_at .newTop box((421/1024:ℝ),(211/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1527 right_from envelope_row1528

return_split cover_node_1521 edge_at .newTop box((421/1024:ℝ),(211/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1526 right_from cover_node_1520

return_split cover_node_1522 edge_at .newTop box((421/1024:ℝ),(211/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1529 right_from envelope_row1530

return_split cover_node_1523 edge_at .newTop box((421/1024:ℝ),(211/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1531 right_from envelope_row1532

return_split cover_node_1524 edge_at .newTop box((421/1024:ℝ),(211/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1522 right_from cover_node_1523

return_split cover_node_1525 edge_at .newTop box((421/1024:ℝ),(211/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1521 right_from cover_node_1524

return_split cover_node_1526 edge_at .newTop box((105/256:ℝ),(211/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (421/1024:ℝ) left_from cover_node_1519 right_from cover_node_1525

return_split cover_node_1527 edge_at .newTop box((211/512:ℝ),(423/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1534 right_from envelope_row1535

return_split cover_node_1528 edge_at .newTop box((211/512:ℝ),(423/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1533 right_from cover_node_1527

return_split cover_node_1529 edge_at .newTop box((211/512:ℝ),(423/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1536 right_from envelope_row1537

return_split cover_node_1530 edge_at .newTop box((211/512:ℝ),(423/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1538 right_from envelope_row1539

return_split cover_node_1531 edge_at .newTop box((211/512:ℝ),(423/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1529 right_from cover_node_1530

return_split cover_node_1532 edge_at .newTop box((211/512:ℝ),(423/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1528 right_from cover_node_1531

return_split cover_node_1533 edge_at .newTop box((423/1024:ℝ),(53/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1541 right_from envelope_row1542

return_split cover_node_1534 edge_at .newTop box((423/1024:ℝ),(53/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1540 right_from cover_node_1533

return_split cover_node_1535 edge_at .newTop box((423/1024:ℝ),(53/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1543 right_from envelope_row1544

return_split cover_node_1536 edge_at .newTop box((423/1024:ℝ),(53/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1545 right_from envelope_row1546

return_split cover_node_1537 edge_at .newTop box((423/1024:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1535 right_from cover_node_1536

return_split cover_node_1538 edge_at .newTop box((423/1024:ℝ),(53/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1534 right_from cover_node_1537

return_split cover_node_1539 edge_at .newTop box((211/512:ℝ),(53/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (423/1024:ℝ) left_from cover_node_1532 right_from cover_node_1538

return_split cover_node_1540 edge_at .newTop box((105/256:ℝ),(53/128:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (211/512:ℝ) left_from cover_node_1526 right_from cover_node_1539

return_split cover_node_1541 edge_at .newTop box((53/128:ℝ),(425/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1548 right_from envelope_row1549

return_split cover_node_1542 edge_at .newTop box((53/128:ℝ),(425/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1547 right_from cover_node_1541

return_split cover_node_1543 edge_at .newTop box((425/1024:ℝ),(213/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1555 right_from envelope_row1556

return_split cover_node_1544 edge_at .newTop box((425/1024:ℝ),(213/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1554 right_from cover_node_1543

return_split cover_node_1545 edge_at .newTop box((53/128:ℝ),(213/512:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (425/1024:ℝ) left_from cover_node_1542 right_from cover_node_1544

return_split cover_node_1546 edge_at .newTop box((213/512:ℝ),(427/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1562 right_from envelope_row1563

return_split cover_node_1547 edge_at .newTop box((213/512:ℝ),(427/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1561 right_from cover_node_1546

return_split cover_node_1548 edge_at .newTop box((427/1024:ℝ),(107/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1569 right_from envelope_row1570

return_split cover_node_1549 edge_at .newTop box((427/1024:ℝ),(107/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1568 right_from cover_node_1548

return_split cover_node_1550 edge_at .newTop box((107/256:ℝ),(429/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1576 right_from envelope_row1577

return_split cover_node_1551 edge_at .newTop box((107/256:ℝ),(429/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1575 right_from cover_node_1550

return_split cover_node_1552 edge_at .newTop box((427/1024:ℝ),(429/1024:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (107/256:ℝ) left_from cover_node_1549 right_from cover_node_1551

return_split cover_node_1553 edge_at .newTop box((213/512:ℝ),(429/1024:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (427/1024:ℝ) left_from cover_node_1547 right_from cover_node_1552

return_split cover_node_1554 edge_at .newTop box((53/128:ℝ),(429/1024:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (213/512:ℝ) left_from cover_node_1545 right_from cover_node_1553

return_split cover_node_1555 edge_at .newTop box((53/128:ℝ),(213/512:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (425/1024:ℝ) left_from envelope_row1550 right_from envelope_row1557

return_split cover_node_1556 edge_at .newTop box((427/1024:ℝ),(429/1024:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (107/256:ℝ) left_from envelope_row1571 right_from envelope_row1578

return_split cover_node_1557 edge_at .newTop box((213/512:ℝ),(429/1024:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (427/1024:ℝ) left_from envelope_row1564 right_from cover_node_1556

return_split cover_node_1558 edge_at .newTop box((53/128:ℝ),(429/1024:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (213/512:ℝ) left_from cover_node_1555 right_from cover_node_1557

return_split cover_node_1559 edge_at .newTop box((53/128:ℝ),(213/512:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (425/1024:ℝ) left_from envelope_row1551 right_from envelope_row1558

return_split cover_node_1560 edge_at .newTop box((427/1024:ℝ),(429/1024:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (107/256:ℝ) left_from envelope_row1572 right_from envelope_row1579

return_split cover_node_1561 edge_at .newTop box((213/512:ℝ),(429/1024:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (427/1024:ℝ) left_from envelope_row1565 right_from cover_node_1560

return_split cover_node_1562 edge_at .newTop box((53/128:ℝ),(429/1024:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (213/512:ℝ) left_from cover_node_1559 right_from cover_node_1561

return_split cover_node_1563 edge_at .newTop box((53/128:ℝ),(429/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from cover_node_1558 right_from cover_node_1562

return_split cover_node_1564 edge_at .newTop box((53/128:ℝ),(213/512:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (425/1024:ℝ) left_from envelope_row1552 right_from envelope_row1559

return_split cover_node_1565 edge_at .newTop box((427/1024:ℝ),(429/1024:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (107/256:ℝ) left_from envelope_row1573 right_from envelope_row1580

return_split cover_node_1566 edge_at .newTop box((213/512:ℝ),(429/1024:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (427/1024:ℝ) left_from envelope_row1566 right_from cover_node_1565

return_split cover_node_1567 edge_at .newTop box((53/128:ℝ),(429/1024:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (213/512:ℝ) left_from cover_node_1564 right_from cover_node_1566

return_split cover_node_1568 edge_at .newTop box((53/128:ℝ),(213/512:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (425/1024:ℝ) left_from envelope_row1553 right_from envelope_row1560

return_split cover_node_1569 edge_at .newTop box((427/1024:ℝ),(429/1024:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (107/256:ℝ) left_from envelope_row1574 right_from envelope_row1581

return_split cover_node_1570 edge_at .newTop box((213/512:ℝ),(429/1024:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (427/1024:ℝ) left_from envelope_row1567 right_from cover_node_1569

return_split cover_node_1571 edge_at .newTop box((53/128:ℝ),(429/1024:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (213/512:ℝ) left_from cover_node_1568 right_from cover_node_1570

return_split cover_node_1572 edge_at .newTop box((53/128:ℝ),(429/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from cover_node_1567 right_from cover_node_1571

return_split cover_node_1573 edge_at .newTop box((53/128:ℝ),(429/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1563 right_from cover_node_1572

return_split cover_node_1574 edge_at .newTop box((53/128:ℝ),(429/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1554 right_from cover_node_1573

return_split cover_node_1575 edge_at .newTop box((105/256:ℝ),(429/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (53/128:ℝ) left_from cover_node_1540 right_from cover_node_1574

return_split cover_node_1576 edge_at .newTop box((405/1024:ℝ),(429/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (105/256:ℝ) left_from cover_node_1513 right_from cover_node_1575

return_split cover_node_1577 edge_at .newTop box((0:ℝ),(429/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (405/1024:ℝ) left_from cover_node_1458 right_from cover_node_1576

return_split cover_node_1578 edge_at .newTop box((429/1024:ℝ),(215/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1583 right_from envelope_row1584

return_split cover_node_1579 edge_at .newTop box((429/1024:ℝ),(215/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1582 right_from cover_node_1578

return_split cover_node_1580 edge_at .newTop box((429/1024:ℝ),(215/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1585 right_from envelope_row1586

return_split cover_node_1581 edge_at .newTop box((429/1024:ℝ),(215/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1587 right_from envelope_row1588

return_split cover_node_1582 edge_at .newTop box((429/1024:ℝ),(215/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1580 right_from cover_node_1581

return_split cover_node_1583 edge_at .newTop box((429/1024:ℝ),(215/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1579 right_from cover_node_1582

return_split cover_node_1584 edge_at .newTop box((215/512:ℝ),(431/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1590 right_from envelope_row1591

return_split cover_node_1585 edge_at .newTop box((215/512:ℝ),(431/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1589 right_from cover_node_1584

return_split cover_node_1586 edge_at .newTop box((215/512:ℝ),(431/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1592 right_from envelope_row1593

return_split cover_node_1587 edge_at .newTop box((215/512:ℝ),(431/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1594 right_from envelope_row1595

return_split cover_node_1588 edge_at .newTop box((215/512:ℝ),(431/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1586 right_from cover_node_1587

return_split cover_node_1589 edge_at .newTop box((215/512:ℝ),(431/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1585 right_from cover_node_1588

return_split cover_node_1590 edge_at .newTop box((429/1024:ℝ),(431/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (215/512:ℝ) left_from cover_node_1583 right_from cover_node_1589

return_split cover_node_1591 edge_at .newTop box((431/1024:ℝ),(27/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1597 right_from envelope_row1598

return_split cover_node_1592 edge_at .newTop box((431/1024:ℝ),(27/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1596 right_from cover_node_1591

return_split cover_node_1593 edge_at .newTop box((431/1024:ℝ),(27/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1599 right_from envelope_row1600

return_split cover_node_1594 edge_at .newTop box((431/1024:ℝ),(27/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1601 right_from envelope_row1602

return_split cover_node_1595 edge_at .newTop box((431/1024:ℝ),(27/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1593 right_from cover_node_1594

return_split cover_node_1596 edge_at .newTop box((431/1024:ℝ),(27/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1592 right_from cover_node_1595

return_split cover_node_1597 edge_at .newTop box((27/64:ℝ),(433/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1604 right_from envelope_row1605

return_split cover_node_1598 edge_at .newTop box((27/64:ℝ),(433/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1603 right_from cover_node_1597

return_split cover_node_1599 edge_at .newTop box((27/64:ℝ),(433/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1606 right_from envelope_row1607

return_split cover_node_1600 edge_at .newTop box((27/64:ℝ),(433/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1608 right_from envelope_row1609

return_split cover_node_1601 edge_at .newTop box((27/64:ℝ),(433/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1599 right_from cover_node_1600

return_split cover_node_1602 edge_at .newTop box((27/64:ℝ),(433/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1598 right_from cover_node_1601

return_split cover_node_1603 edge_at .newTop box((431/1024:ℝ),(433/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (27/64:ℝ) left_from cover_node_1596 right_from cover_node_1602

return_split cover_node_1604 edge_at .newTop box((429/1024:ℝ),(433/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (431/1024:ℝ) left_from cover_node_1590 right_from cover_node_1603

return_split cover_node_1605 edge_at .newTop box((433/1024:ℝ),(217/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1611 right_from envelope_row1612

return_split cover_node_1606 edge_at .newTop box((433/1024:ℝ),(217/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1610 right_from cover_node_1605

return_split cover_node_1607 edge_at .newTop box((217/512:ℝ),(435/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1618 right_from envelope_row1619

return_split cover_node_1608 edge_at .newTop box((217/512:ℝ),(435/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1617 right_from cover_node_1607

return_split cover_node_1609 edge_at .newTop box((433/1024:ℝ),(435/1024:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (217/512:ℝ) left_from cover_node_1606 right_from cover_node_1608

return_split cover_node_1610 edge_at .newTop box((435/1024:ℝ),(109/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1625 right_from envelope_row1626

return_split cover_node_1611 edge_at .newTop box((435/1024:ℝ),(109/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1624 right_from cover_node_1610

return_split cover_node_1612 edge_at .newTop box((109/256:ℝ),(437/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1632 right_from envelope_row1633

return_split cover_node_1613 edge_at .newTop box((109/256:ℝ),(437/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1631 right_from cover_node_1612

return_split cover_node_1614 edge_at .newTop box((437/1024:ℝ),(219/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1639 right_from envelope_row1640

return_split cover_node_1615 edge_at .newTop box((437/1024:ℝ),(219/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1638 right_from cover_node_1614

return_split cover_node_1616 edge_at .newTop box((109/256:ℝ),(219/512:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (437/1024:ℝ) left_from cover_node_1613 right_from cover_node_1615

return_split cover_node_1617 edge_at .newTop box((435/1024:ℝ),(219/512:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (109/256:ℝ) left_from cover_node_1611 right_from cover_node_1616

return_split cover_node_1618 edge_at .newTop box((433/1024:ℝ),(219/512:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (435/1024:ℝ) left_from cover_node_1609 right_from cover_node_1617

return_split cover_node_1619 edge_at .newTop box((433/1024:ℝ),(435/1024:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (217/512:ℝ) left_from envelope_row1613 right_from envelope_row1620

return_split cover_node_1620 edge_at .newTop box((109/256:ℝ),(219/512:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (437/1024:ℝ) left_from envelope_row1634 right_from envelope_row1641

return_split cover_node_1621 edge_at .newTop box((435/1024:ℝ),(219/512:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (109/256:ℝ) left_from envelope_row1627 right_from cover_node_1620

return_split cover_node_1622 edge_at .newTop box((433/1024:ℝ),(219/512:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (435/1024:ℝ) left_from cover_node_1619 right_from cover_node_1621

return_split cover_node_1623 edge_at .newTop box((433/1024:ℝ),(435/1024:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (217/512:ℝ) left_from envelope_row1614 right_from envelope_row1621

return_split cover_node_1624 edge_at .newTop box((109/256:ℝ),(219/512:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (437/1024:ℝ) left_from envelope_row1635 right_from envelope_row1642

return_split cover_node_1625 edge_at .newTop box((435/1024:ℝ),(219/512:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (109/256:ℝ) left_from envelope_row1628 right_from cover_node_1624

return_split cover_node_1626 edge_at .newTop box((433/1024:ℝ),(219/512:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (435/1024:ℝ) left_from cover_node_1623 right_from cover_node_1625

return_split cover_node_1627 edge_at .newTop box((433/1024:ℝ),(219/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from cover_node_1622 right_from cover_node_1626

return_split cover_node_1628 edge_at .newTop box((433/1024:ℝ),(435/1024:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (217/512:ℝ) left_from envelope_row1615 right_from envelope_row1622

return_split cover_node_1629 edge_at .newTop box((109/256:ℝ),(219/512:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (437/1024:ℝ) left_from envelope_row1636 right_from envelope_row1643

return_split cover_node_1630 edge_at .newTop box((435/1024:ℝ),(219/512:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (109/256:ℝ) left_from envelope_row1629 right_from cover_node_1629

return_split cover_node_1631 edge_at .newTop box((433/1024:ℝ),(219/512:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (435/1024:ℝ) left_from cover_node_1628 right_from cover_node_1630

return_split cover_node_1632 edge_at .newTop box((433/1024:ℝ),(435/1024:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (217/512:ℝ) left_from envelope_row1616 right_from envelope_row1623

return_split cover_node_1633 edge_at .newTop box((109/256:ℝ),(219/512:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (437/1024:ℝ) left_from envelope_row1637 right_from envelope_row1644

return_split cover_node_1634 edge_at .newTop box((435/1024:ℝ),(219/512:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (109/256:ℝ) left_from envelope_row1630 right_from cover_node_1633

return_split cover_node_1635 edge_at .newTop box((433/1024:ℝ),(219/512:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (435/1024:ℝ) left_from cover_node_1632 right_from cover_node_1634

return_split cover_node_1636 edge_at .newTop box((433/1024:ℝ),(219/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from cover_node_1631 right_from cover_node_1635

return_split cover_node_1637 edge_at .newTop box((433/1024:ℝ),(219/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1627 right_from cover_node_1636

return_split cover_node_1638 edge_at .newTop box((433/1024:ℝ),(219/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1618 right_from cover_node_1637

return_split cover_node_1639 edge_at .newTop box((429/1024:ℝ),(219/512:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (433/1024:ℝ) left_from cover_node_1604 right_from cover_node_1638

return_split cover_node_1640 edge_at .newTop box((219/512:ℝ),(439/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1646 right_from envelope_row1647

return_split cover_node_1641 edge_at .newTop box((219/512:ℝ),(439/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1645 right_from cover_node_1640

return_split cover_node_1642 edge_at .newTop box((219/512:ℝ),(439/1024:ℝ),(31/64:ℝ),(127/256:ℝ)) along p cut_at (63/128:ℝ) left_from envelope_row1649 right_from envelope_row1650

return_split cover_node_1643 edge_at .newTop box((219/512:ℝ),(439/1024:ℝ),(15/32:ℝ),(127/256:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1648 right_from cover_node_1642

return_split cover_node_1644 edge_at .newTop box((219/512:ℝ),(439/1024:ℝ),(0:ℝ),(127/256:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1641 right_from cover_node_1643

return_split cover_node_1645 edge_at .newTop box((439/1024:ℝ),(55/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1653 right_from envelope_row1654

return_split cover_node_1646 edge_at .newTop box((439/1024:ℝ),(55/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1652 right_from cover_node_1645

return_split cover_node_1647 edge_at .newTop box((439/1024:ℝ),(55/128:ℝ),(31/64:ℝ),(127/256:ℝ)) along p cut_at (63/128:ℝ) left_from envelope_row1656 right_from envelope_row1657

return_split cover_node_1648 edge_at .newTop box((439/1024:ℝ),(55/128:ℝ),(15/32:ℝ),(127/256:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1655 right_from cover_node_1647

return_split cover_node_1649 edge_at .newTop box((439/1024:ℝ),(55/128:ℝ),(0:ℝ),(127/256:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1646 right_from cover_node_1648

return_split cover_node_1650 edge_at .newTop box((219/512:ℝ),(55/128:ℝ),(0:ℝ),(127/256:ℝ)) along δ cut_at (439/1024:ℝ) left_from cover_node_1644 right_from cover_node_1649

return_split cover_node_1651 edge_at .newTop box((55/128:ℝ),(111/256:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1660 right_from envelope_row1661

return_split cover_node_1652 edge_at .newTop box((55/128:ℝ),(111/256:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1659 right_from cover_node_1651

return_split cover_node_1653 edge_at .newTop box((55/128:ℝ),(111/256:ℝ),(31/64:ℝ),(127/256:ℝ)) along p cut_at (63/128:ℝ) left_from envelope_row1663 right_from envelope_row1664

return_split cover_node_1654 edge_at .newTop box((55/128:ℝ),(111/256:ℝ),(15/32:ℝ),(127/256:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1662 right_from cover_node_1653

return_split cover_node_1655 edge_at .newTop box((55/128:ℝ),(111/256:ℝ),(0:ℝ),(127/256:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1652 right_from cover_node_1654

return_split cover_node_1656 edge_at .newTop box((111/256:ℝ),(7/16:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1667 right_from envelope_row1668

return_split cover_node_1657 edge_at .newTop box((111/256:ℝ),(7/16:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1666 right_from cover_node_1656

return_split cover_node_1658 edge_at .newTop box((111/256:ℝ),(7/16:ℝ),(31/64:ℝ),(127/256:ℝ)) along p cut_at (63/128:ℝ) left_from envelope_row1670 right_from envelope_row1671

return_split cover_node_1659 edge_at .newTop box((111/256:ℝ),(7/16:ℝ),(15/32:ℝ),(127/256:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1669 right_from cover_node_1658

return_split cover_node_1660 edge_at .newTop box((111/256:ℝ),(7/16:ℝ),(0:ℝ),(127/256:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1657 right_from cover_node_1659

return_split cover_node_1661 edge_at .newTop box((55/128:ℝ),(7/16:ℝ),(0:ℝ),(127/256:ℝ)) along δ cut_at (111/256:ℝ) left_from cover_node_1655 right_from cover_node_1660

return_split cover_node_1662 edge_at .newTop box((219/512:ℝ),(7/16:ℝ),(0:ℝ),(127/256:ℝ)) along δ cut_at (55/128:ℝ) left_from cover_node_1650 right_from cover_node_1661

return_split cover_node_1663 edge_at .newTop box((439/1024:ℝ),(111/256:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (55/128:ℝ) left_from envelope_row1658 right_from envelope_row1665

return_split cover_node_1664 edge_at .newTop box((219/512:ℝ),(111/256:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (439/1024:ℝ) left_from envelope_row1651 right_from cover_node_1663

return_split cover_node_1665 edge_at .newTop box((111/256:ℝ),(7/16:ℝ),(127/256:ℝ),(511/1024:ℝ)) along p cut_at (255/512:ℝ) left_from envelope_row1672 right_from envelope_row1673

return_split cover_node_1666 edge_at .newTop box((111/256:ℝ),(7/16:ℝ),(511/1024:ℝ),(2047/4096:ℝ)) along p cut_at (1023/2048:ℝ) left_from envelope_row1674 right_from envelope_row1675

return_split cover_node_1667 edge_at .newTop box((111/256:ℝ),(7/16:ℝ),(127/256:ℝ),(2047/4096:ℝ)) along p cut_at (511/1024:ℝ) left_from cover_node_1665 right_from cover_node_1666

return_split cover_node_1668 edge_at .newTop box((111/256:ℝ),(223/512:ℝ),(2047/4096:ℝ),(8191/16384:ℝ)) along p cut_at (4095/8192:ℝ) left_from envelope_row1676 right_from envelope_row1677

return_split cover_node_1669 edge_at .newTop box((111/256:ℝ),(445/1024:ℝ),(8191/16384:ℝ),(32767/65536:ℝ)) along p cut_at (16383/32768:ℝ) left_from envelope_row1678 right_from envelope_row1679

return_split cover_node_1670 edge_at .newTop box((111/256:ℝ),(889/2048:ℝ),(32767/65536:ℝ),(131071/262144:ℝ)) along p cut_at (65535/131072:ℝ) left_from envelope_row1680 right_from envelope_row1681

return_split cover_node_1671 edge_at .newTop box((1777/4096:ℝ),(889/2048:ℝ),(262143/524288:ℝ),(1048575/2097152:ℝ)) along p cut_at (524287/1048576:ℝ) left_from envelope_row1684 right_from envelope_row1685

return_split cover_node_1672 edge_at .newTop box((1777/4096:ℝ),(889/2048:ℝ),(131071/262144:ℝ),(1048575/2097152:ℝ)) along p cut_at (262143/524288:ℝ) left_from envelope_row1683 right_from cover_node_1671

return_split cover_node_1673 edge_at .newTop box((7109/16384:ℝ),(3555/8192:ℝ),(4194303/8388608:ℝ),(16777215/33554432:ℝ)) along p cut_at (8388607/16777216:ℝ) left_from envelope_row1689 right_from envelope_row1690

return_split cover_node_1674 edge_at .newTop box((7109/16384:ℝ),(3555/8192:ℝ),(2097151/4194304:ℝ),(16777215/33554432:ℝ)) along p cut_at (4194303/8388608:ℝ) left_from envelope_row1688 right_from cover_node_1673

return_split cover_node_1675 edge_at .newTop box((14219/32768:ℝ),(113753/262144:ℝ),(33554431/67108864:ℝ),(1/2:ℝ)) along δ cut_at (227505/524288:ℝ) left_from envelope_row1693 right_from envelope_row1694

return_split cover_node_1676 edge_at .newTop box((56877/131072:ℝ),(3555/8192:ℝ),(33554431/67108864:ℝ),(1/2:ℝ)) along δ cut_at (28439/65536:ℝ) left_from envelope_row1696 right_from envelope_row1697

return_split cover_node_1677 edge_at .newTop box((113753/262144:ℝ),(3555/8192:ℝ),(33554431/67108864:ℝ),(1/2:ℝ)) along δ cut_at (56877/131072:ℝ) left_from envelope_row1695 right_from cover_node_1676

return_split cover_node_1678 edge_at .newTop box((14219/32768:ℝ),(3555/8192:ℝ),(33554431/67108864:ℝ),(1/2:ℝ)) along δ cut_at (113753/262144:ℝ) left_from cover_node_1675 right_from cover_node_1677

return_split cover_node_1679 edge_at .newTop box((14219/32768:ℝ),(3555/8192:ℝ),(16777215/33554432:ℝ),(1/2:ℝ)) along p cut_at (33554431/67108864:ℝ) left_from envelope_row1692 right_from cover_node_1678

return_split cover_node_1680 edge_at .newTop box((7109/16384:ℝ),(3555/8192:ℝ),(16777215/33554432:ℝ),(1/2:ℝ)) along δ cut_at (14219/32768:ℝ) left_from envelope_row1691 right_from cover_node_1679

return_split cover_node_1681 edge_at .newTop box((7109/16384:ℝ),(3555/8192:ℝ),(2097151/4194304:ℝ),(1/2:ℝ)) along p cut_at (16777215/33554432:ℝ) left_from cover_node_1674 right_from cover_node_1680

return_split cover_node_1682 edge_at .newTop box((1777/4096:ℝ),(3555/8192:ℝ),(2097151/4194304:ℝ),(1/2:ℝ)) along δ cut_at (7109/16384:ℝ) left_from envelope_row1687 right_from cover_node_1681

return_split cover_node_1683 edge_at .newTop box((1777/4096:ℝ),(3555/8192:ℝ),(1048575/2097152:ℝ),(1/2:ℝ)) along p cut_at (2097151/4194304:ℝ) left_from envelope_row1686 right_from cover_node_1682

return_split cover_node_1684 edge_at .newTop box((1777/4096:ℝ),(889/2048:ℝ),(1048575/2097152:ℝ),(1/2:ℝ)) along δ cut_at (3555/8192:ℝ) left_from cover_node_1683 right_from envelope_row1698

return_split cover_node_1685 edge_at .newTop box((1777/4096:ℝ),(889/2048:ℝ),(131071/262144:ℝ),(1/2:ℝ)) along p cut_at (1048575/2097152:ℝ) left_from cover_node_1672 right_from cover_node_1684

return_split cover_node_1686 edge_at .newTop box((111/256:ℝ),(889/2048:ℝ),(131071/262144:ℝ),(1/2:ℝ)) along δ cut_at (1777/4096:ℝ) left_from envelope_row1682 right_from cover_node_1685

return_split cover_node_1687 edge_at .newTop box((111/256:ℝ),(889/2048:ℝ),(32767/65536:ℝ),(1/2:ℝ)) along p cut_at (131071/262144:ℝ) left_from cover_node_1670 right_from cover_node_1686

return_split cover_node_1688 edge_at .newTop box((111/256:ℝ),(445/1024:ℝ),(32767/65536:ℝ),(1/2:ℝ)) along δ cut_at (889/2048:ℝ) left_from cover_node_1687 right_from envelope_row1699

return_split cover_node_1689 edge_at .newTop box((111/256:ℝ),(445/1024:ℝ),(8191/16384:ℝ),(1/2:ℝ)) along p cut_at (32767/65536:ℝ) left_from cover_node_1669 right_from cover_node_1688

return_split cover_node_1690 edge_at .newTop box((111/256:ℝ),(223/512:ℝ),(8191/16384:ℝ),(1/2:ℝ)) along δ cut_at (445/1024:ℝ) left_from cover_node_1689 right_from envelope_row1700

return_split cover_node_1691 edge_at .newTop box((111/256:ℝ),(223/512:ℝ),(2047/4096:ℝ),(1/2:ℝ)) along p cut_at (8191/16384:ℝ) left_from cover_node_1668 right_from cover_node_1690

return_split cover_node_1692 edge_at .newTop box((111/256:ℝ),(7/16:ℝ),(2047/4096:ℝ),(1/2:ℝ)) along δ cut_at (223/512:ℝ) left_from cover_node_1691 right_from envelope_row1701

return_split cover_node_1693 edge_at .newTop box((111/256:ℝ),(7/16:ℝ),(127/256:ℝ),(1/2:ℝ)) along p cut_at (2047/4096:ℝ) left_from cover_node_1667 right_from cover_node_1692

return_split cover_node_1694 edge_at .newTop box((219/512:ℝ),(7/16:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (111/256:ℝ) left_from cover_node_1664 right_from cover_node_1693

return_split cover_node_1695 edge_at .newTop box((219/512:ℝ),(7/16:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from cover_node_1662 right_from cover_node_1694

return_split cover_node_1696 edge_at .newTop box((429/1024:ℝ),(7/16:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (219/512:ℝ) left_from cover_node_1639 right_from cover_node_1695

return_split cover_node_1697 edge_at .newTop box((7/16:ℝ),(225/512:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1703 right_from envelope_row1704

return_split cover_node_1698 edge_at .newTop box((7/16:ℝ),(225/512:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1702 right_from cover_node_1697

return_split cover_node_1699 edge_at .newTop box((7/16:ℝ),(225/512:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1705 right_from envelope_row1706

return_split cover_node_1700 edge_at .newTop box((7/16:ℝ),(225/512:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1707 right_from envelope_row1708

return_split cover_node_1701 edge_at .newTop box((7/16:ℝ),(225/512:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1699 right_from cover_node_1700

return_split cover_node_1702 edge_at .newTop box((7/16:ℝ),(225/512:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1698 right_from cover_node_1701

return_split cover_node_1703 edge_at .newTop box((225/512:ℝ),(453/1024:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1710 right_from envelope_row1711

return_split cover_node_1704 edge_at .newTop box((225/512:ℝ),(453/1024:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1709 right_from cover_node_1703

return_split cover_node_1705 edge_at .newTop box((225/512:ℝ),(453/1024:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1712 right_from envelope_row1713

return_split cover_node_1706 edge_at .newTop box((225/512:ℝ),(453/1024:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1714 right_from envelope_row1715

return_split cover_node_1707 edge_at .newTop box((225/512:ℝ),(453/1024:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1705 right_from cover_node_1706

return_split cover_node_1708 edge_at .newTop box((225/512:ℝ),(453/1024:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1704 right_from cover_node_1707

return_split cover_node_1709 edge_at .newTop box((7/16:ℝ),(453/1024:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (225/512:ℝ) left_from cover_node_1702 right_from cover_node_1708

return_split cover_node_1710 edge_at .newTop box((453/1024:ℝ),(57/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1717 right_from envelope_row1718

return_split cover_node_1711 edge_at .newTop box((453/1024:ℝ),(57/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1716 right_from cover_node_1710

return_split cover_node_1712 edge_at .newTop box((453/1024:ℝ),(57/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1719 right_from envelope_row1720

return_split cover_node_1713 edge_at .newTop box((453/1024:ℝ),(57/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1721 right_from envelope_row1722

return_split cover_node_1714 edge_at .newTop box((453/1024:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1712 right_from cover_node_1713

return_split cover_node_1715 edge_at .newTop box((453/1024:ℝ),(57/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1711 right_from cover_node_1714

return_split cover_node_1716 edge_at .newTop box((57/128:ℝ),(29/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1724 right_from envelope_row1725

return_split cover_node_1717 edge_at .newTop box((57/128:ℝ),(29/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1723 right_from cover_node_1716

return_split cover_node_1718 edge_at .newTop box((57/128:ℝ),(29/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1726 right_from envelope_row1727

return_split cover_node_1719 edge_at .newTop box((57/128:ℝ),(29/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1728 right_from envelope_row1729

return_split cover_node_1720 edge_at .newTop box((57/128:ℝ),(29/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1718 right_from cover_node_1719

return_split cover_node_1721 edge_at .newTop box((57/128:ℝ),(29/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1717 right_from cover_node_1720

return_split cover_node_1722 edge_at .newTop box((453/1024:ℝ),(29/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (57/128:ℝ) left_from cover_node_1715 right_from cover_node_1721

return_split cover_node_1723 edge_at .newTop box((7/16:ℝ),(29/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (453/1024:ℝ) left_from cover_node_1709 right_from cover_node_1722

return_split cover_node_1724 edge_at .newTop box((29/64:ℝ),(59/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1731 right_from envelope_row1732

return_split cover_node_1725 edge_at .newTop box((29/64:ℝ),(59/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1730 right_from cover_node_1724

return_split cover_node_1726 edge_at .newTop box((29/64:ℝ),(59/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1733 right_from envelope_row1734

return_split cover_node_1727 edge_at .newTop box((29/64:ℝ),(59/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1735 right_from envelope_row1736

return_split cover_node_1728 edge_at .newTop box((29/64:ℝ),(59/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1726 right_from cover_node_1727

return_split cover_node_1729 edge_at .newTop box((29/64:ℝ),(59/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1725 right_from cover_node_1728

return_split cover_node_1730 edge_at .newTop box((59/128:ℝ),(15/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1738 right_from envelope_row1739

return_split cover_node_1731 edge_at .newTop box((59/128:ℝ),(15/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1737 right_from cover_node_1730

return_split cover_node_1732 edge_at .newTop box((59/128:ℝ),(15/32:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1740 right_from envelope_row1741

return_split cover_node_1733 edge_at .newTop box((59/128:ℝ),(15/32:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1742 right_from envelope_row1743

return_split cover_node_1734 edge_at .newTop box((59/128:ℝ),(15/32:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1732 right_from cover_node_1733

return_split cover_node_1735 edge_at .newTop box((59/128:ℝ),(15/32:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1731 right_from cover_node_1734

return_split cover_node_1736 edge_at .newTop box((29/64:ℝ),(15/32:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (59/128:ℝ) left_from cover_node_1729 right_from cover_node_1735

return_split cover_node_1737 edge_at .newTop box((15/32:ℝ),(61/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1745 right_from envelope_row1746

return_split cover_node_1738 edge_at .newTop box((15/32:ℝ),(61/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1744 right_from cover_node_1737

return_split cover_node_1739 edge_at .newTop box((15/32:ℝ),(61/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1747 right_from envelope_row1748

return_split cover_node_1740 edge_at .newTop box((15/32:ℝ),(61/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1749 right_from envelope_row1750

return_split cover_node_1741 edge_at .newTop box((15/32:ℝ),(61/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1739 right_from cover_node_1740

return_split cover_node_1742 edge_at .newTop box((15/32:ℝ),(61/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1738 right_from cover_node_1741

return_split cover_node_1743 edge_at .newTop box((61/128:ℝ),(31/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1752 right_from envelope_row1753

return_split cover_node_1744 edge_at .newTop box((61/128:ℝ),(31/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1751 right_from cover_node_1743

return_split cover_node_1745 edge_at .newTop box((61/128:ℝ),(31/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1754 right_from envelope_row1755

return_split cover_node_1746 edge_at .newTop box((61/128:ℝ),(31/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1756 right_from envelope_row1757

return_split cover_node_1747 edge_at .newTop box((61/128:ℝ),(31/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1745 right_from cover_node_1746

return_split cover_node_1748 edge_at .newTop box((61/128:ℝ),(31/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1744 right_from cover_node_1747

return_split cover_node_1749 edge_at .newTop box((15/32:ℝ),(31/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (61/128:ℝ) left_from cover_node_1742 right_from cover_node_1748

return_split cover_node_1750 edge_at .newTop box((29/64:ℝ),(31/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (15/32:ℝ) left_from cover_node_1736 right_from cover_node_1749

return_split cover_node_1751 edge_at .newTop box((7/16:ℝ),(31/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (29/64:ℝ) left_from cover_node_1723 right_from cover_node_1750

return_split cover_node_1752 edge_at .newTop box((31/64:ℝ),(63/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1759 right_from envelope_row1760

return_split cover_node_1753 edge_at .newTop box((31/64:ℝ),(63/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1758 right_from cover_node_1752

return_split cover_node_1754 edge_at .newTop box((31/64:ℝ),(63/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1761 right_from envelope_row1762

return_split cover_node_1755 edge_at .newTop box((31/64:ℝ),(63/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1763 right_from envelope_row1764

return_split cover_node_1756 edge_at .newTop box((31/64:ℝ),(63/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1754 right_from cover_node_1755

return_split cover_node_1757 edge_at .newTop box((31/64:ℝ),(63/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1753 right_from cover_node_1756

return_split cover_node_1758 edge_at .newTop box((63/128:ℝ),(1/2:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1766 right_from envelope_row1767

return_split cover_node_1759 edge_at .newTop box((63/128:ℝ),(1/2:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1765 right_from cover_node_1758

return_split cover_node_1760 edge_at .newTop box((63/128:ℝ),(1/2:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1768 right_from envelope_row1769

return_split cover_node_1761 edge_at .newTop box((63/128:ℝ),(1/2:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1770 right_from envelope_row1771

return_split cover_node_1762 edge_at .newTop box((63/128:ℝ),(1/2:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1760 right_from cover_node_1761

return_split cover_node_1763 edge_at .newTop box((63/128:ℝ),(1/2:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1759 right_from cover_node_1762

return_split cover_node_1764 edge_at .newTop box((31/64:ℝ),(1/2:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (63/128:ℝ) left_from cover_node_1757 right_from cover_node_1763

return_split cover_node_1765 edge_at .newTop box((1/2:ℝ),(65/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1773 right_from envelope_row1774

return_split cover_node_1766 edge_at .newTop box((1/2:ℝ),(65/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1772 right_from cover_node_1765

return_split cover_node_1767 edge_at .newTop box((1/2:ℝ),(65/128:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1775 right_from envelope_row1776

return_split cover_node_1768 edge_at .newTop box((1/2:ℝ),(65/128:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1777 right_from envelope_row1778

return_split cover_node_1769 edge_at .newTop box((1/2:ℝ),(65/128:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1767 right_from cover_node_1768

return_split cover_node_1770 edge_at .newTop box((1/2:ℝ),(65/128:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1766 right_from cover_node_1769

return_split cover_node_1771 edge_at .newTop box((65/128:ℝ),(33/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1780 right_from envelope_row1781

return_split cover_node_1772 edge_at .newTop box((65/128:ℝ),(33/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1779 right_from cover_node_1771

return_split cover_node_1773 edge_at .newTop box((65/128:ℝ),(33/64:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from envelope_row1782 right_from envelope_row1783

return_split cover_node_1774 edge_at .newTop box((65/128:ℝ),(33/64:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from envelope_row1784 right_from envelope_row1785

return_split cover_node_1775 edge_at .newTop box((65/128:ℝ),(33/64:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1773 right_from cover_node_1774

return_split cover_node_1776 edge_at .newTop box((65/128:ℝ),(33/64:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1772 right_from cover_node_1775

return_split cover_node_1777 edge_at .newTop box((1/2:ℝ),(33/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (65/128:ℝ) left_from cover_node_1770 right_from cover_node_1776

return_split cover_node_1778 edge_at .newTop box((31/64:ℝ),(33/64:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (1/2:ℝ) left_from cover_node_1764 right_from cover_node_1777

return_split cover_node_1779 edge_at .newTop box((33/64:ℝ),(67/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1787 right_from envelope_row1788

return_split cover_node_1780 edge_at .newTop box((33/64:ℝ),(67/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1786 right_from cover_node_1779

return_split cover_node_1781 edge_at .newTop box((67/128:ℝ),(17/32:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1794 right_from envelope_row1795

return_split cover_node_1782 edge_at .newTop box((67/128:ℝ),(17/32:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1793 right_from cover_node_1781

return_split cover_node_1783 edge_at .newTop box((33/64:ℝ),(17/32:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (67/128:ℝ) left_from cover_node_1780 right_from cover_node_1782

return_split cover_node_1784 edge_at .newTop box((17/32:ℝ),(69/128:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1801 right_from envelope_row1802

return_split cover_node_1785 edge_at .newTop box((17/32:ℝ),(69/128:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1800 right_from cover_node_1784

return_split cover_node_1786 edge_at .newTop box((69/128:ℝ),(35/64:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1808 right_from envelope_row1809

return_split cover_node_1787 edge_at .newTop box((69/128:ℝ),(35/64:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1807 right_from cover_node_1786

return_split cover_node_1788 edge_at .newTop box((35/64:ℝ),(3/4:ℝ),(3/8:ℝ),(15/32:ℝ)) along p cut_at (7/16:ℝ) left_from envelope_row1815 right_from envelope_row1816

return_split cover_node_1789 edge_at .newTop box((35/64:ℝ),(3/4:ℝ),(0:ℝ),(15/32:ℝ)) along p cut_at (3/8:ℝ) left_from envelope_row1814 right_from cover_node_1788

return_split cover_node_1790 edge_at .newTop box((69/128:ℝ),(3/4:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (35/64:ℝ) left_from cover_node_1787 right_from cover_node_1789

return_split cover_node_1791 edge_at .newTop box((17/32:ℝ),(3/4:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (69/128:ℝ) left_from cover_node_1785 right_from cover_node_1790

return_split cover_node_1792 edge_at .newTop box((33/64:ℝ),(3/4:ℝ),(0:ℝ),(15/32:ℝ)) along δ cut_at (17/32:ℝ) left_from cover_node_1783 right_from cover_node_1791

return_split cover_node_1793 edge_at .newTop box((33/64:ℝ),(17/32:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (67/128:ℝ) left_from envelope_row1789 right_from envelope_row1796

return_split cover_node_1794 edge_at .newTop box((69/128:ℝ),(3/4:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (35/64:ℝ) left_from envelope_row1810 right_from envelope_row1817

return_split cover_node_1795 edge_at .newTop box((17/32:ℝ),(3/4:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (69/128:ℝ) left_from envelope_row1803 right_from cover_node_1794

return_split cover_node_1796 edge_at .newTop box((33/64:ℝ),(3/4:ℝ),(15/32:ℝ),(31/64:ℝ)) along δ cut_at (17/32:ℝ) left_from cover_node_1793 right_from cover_node_1795

return_split cover_node_1797 edge_at .newTop box((33/64:ℝ),(17/32:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (67/128:ℝ) left_from envelope_row1790 right_from envelope_row1797

return_split cover_node_1798 edge_at .newTop box((69/128:ℝ),(3/4:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (35/64:ℝ) left_from envelope_row1811 right_from envelope_row1818

return_split cover_node_1799 edge_at .newTop box((17/32:ℝ),(3/4:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (69/128:ℝ) left_from envelope_row1804 right_from cover_node_1798

return_split cover_node_1800 edge_at .newTop box((33/64:ℝ),(3/4:ℝ),(31/64:ℝ),(63/128:ℝ)) along δ cut_at (17/32:ℝ) left_from cover_node_1797 right_from cover_node_1799

return_split cover_node_1801 edge_at .newTop box((33/64:ℝ),(3/4:ℝ),(15/32:ℝ),(63/128:ℝ)) along p cut_at (31/64:ℝ) left_from cover_node_1796 right_from cover_node_1800

return_split cover_node_1802 edge_at .newTop box((33/64:ℝ),(17/32:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (67/128:ℝ) left_from envelope_row1791 right_from envelope_row1798

return_split cover_node_1803 edge_at .newTop box((69/128:ℝ),(3/4:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (35/64:ℝ) left_from envelope_row1812 right_from envelope_row1819

return_split cover_node_1804 edge_at .newTop box((17/32:ℝ),(3/4:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (69/128:ℝ) left_from envelope_row1805 right_from cover_node_1803

return_split cover_node_1805 edge_at .newTop box((33/64:ℝ),(3/4:ℝ),(63/128:ℝ),(127/256:ℝ)) along δ cut_at (17/32:ℝ) left_from cover_node_1802 right_from cover_node_1804

return_split cover_node_1806 edge_at .newTop box((33/64:ℝ),(17/32:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (67/128:ℝ) left_from envelope_row1792 right_from envelope_row1799

return_split cover_node_1807 edge_at .newTop box((69/128:ℝ),(3/4:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (35/64:ℝ) left_from envelope_row1813 right_from envelope_row1820

return_split cover_node_1808 edge_at .newTop box((17/32:ℝ),(3/4:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (69/128:ℝ) left_from envelope_row1806 right_from cover_node_1807

return_split cover_node_1809 edge_at .newTop box((33/64:ℝ),(3/4:ℝ),(127/256:ℝ),(1/2:ℝ)) along δ cut_at (17/32:ℝ) left_from cover_node_1806 right_from cover_node_1808

return_split cover_node_1810 edge_at .newTop box((33/64:ℝ),(3/4:ℝ),(63/128:ℝ),(1/2:ℝ)) along p cut_at (127/256:ℝ) left_from cover_node_1805 right_from cover_node_1809

return_split cover_node_1811 edge_at .newTop box((33/64:ℝ),(3/4:ℝ),(15/32:ℝ),(1/2:ℝ)) along p cut_at (63/128:ℝ) left_from cover_node_1801 right_from cover_node_1810

return_split cover_node_1812 edge_at .newTop box((33/64:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along p cut_at (15/32:ℝ) left_from cover_node_1792 right_from cover_node_1811

return_split cover_node_1813 edge_at .newTop box((31/64:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (33/64:ℝ) left_from cover_node_1778 right_from cover_node_1812

return_split cover_node_1814 edge_at .newTop box((7/16:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (31/64:ℝ) left_from cover_node_1751 right_from cover_node_1813

return_split cover_node_1815 edge_at .newTop box((429/1024:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (7/16:ℝ) left_from cover_node_1696 right_from cover_node_1814

return_split cover_node_1816 edge_at .newTop box((0:ℝ),(3/4:ℝ),(0:ℝ),(1/2:ℝ)) along δ cut_at (429/1024:ℝ) left_from cover_node_1577 right_from cover_node_1815

theorem closed_envelope_return_cover (e : Edge) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  cases e with
  | oldSmall => exact cover_node_446 hδ hp
  | oldSwitch => exact cover_node_893 hδ hp
  | newSwitch => exact cover_node_1340 hδ hp
  | newTop => exact cover_node_1816 hδ hp

end
end Qrh.JointDetector.BoundarySeedReturn.FinalEdges
