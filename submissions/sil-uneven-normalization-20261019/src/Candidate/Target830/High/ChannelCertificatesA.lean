import Candidate.Target830.High.ChannelDefs

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open Target830

theorem channel_A_lo_0 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (17/500:ℝ) delta 0 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (9074766777951874603378133294507/115699290661993750000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (707343066729626840188154958889/2082587231915887500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (928937410931989857087224807/2082587231915887500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (192043952520141849215411/1041293615957943750:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (17/500:ℝ) delta 0-highFee)=
      (9074766777951874603378133294507/115699290661993750000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (707343066729626840188154958889/2082587231915887500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (928937410931989857087224807/2082587231915887500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (192043952520141849215411/1041293615957943750:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_lo_1 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (17/500:ℝ) delta 1 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (367273808086970046738126309659/18268309051893750000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (24790602422408314991868155731/109609854311362500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (42858676945306127330380253/109609854311362500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (10113431286625262063969/54804927155681250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (17/500:ℝ) delta 1-highFee)=
      (367273808086970046738126309659/18268309051893750000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (24790602422408314991868155731/109609854311362500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (42858676945306127330380253/109609854311362500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (10113431286625262063969/54804927155681250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_lo_2 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (17/500:ℝ) delta 2 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (42849429162919688556647436553/6089436350631250000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (12252507644749680357792155731/109609854311362500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (22449532635147073232380253/109609854311362500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (5463518790771428063969/54804927155681250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (17/500:ℝ) delta 2-highFee)=
      (42849429162919688556647436553/6089436350631250000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (12252507644749680357792155731/109609854311362500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (22449532635147073232380253/109609854311362500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (5463518790771428063969/54804927155681250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_lo_3 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (17/500:ℝ) delta 3 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (717204828478912292510607856757/1141769315743359375000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (310424140330167155309676609458399/3425307947230078125000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (315170959017352370545384847201/1712653973615039062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (79682035915474493406850733/856326986807519531250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (17/500:ℝ) delta 3-highFee)=
      (717204828478912292510607856757/1141769315743359375000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (310424140330167155309676609458399/3425307947230078125000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (315170959017352370545384847201/1712653973615039062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (79682035915474493406850733/856326986807519531250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_lo_4 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (17/500:ℝ) delta 4 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (30915126367338205636566584994898313/2283538631486718750000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (833507525738321734359430418969341/6850615894460156250000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (353779132885242687402186726467/1712653973615039062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (84117149004538685582523611/856326986807519531250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (17/500:ℝ) delta 4-highFee)=
      (30915126367338205636566584994898313/2283538631486718750000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (833507525738321734359430418969341/6850615894460156250000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (353779132885242687402186726467/1712653973615039062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (84117149004538685582523611/856326986807519531250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_lo_5 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (17/500:ℝ) delta 5 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (4949341613633426750802939167745609/761179543828906250000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (688574078601801022616773904698639/6850615894460156250000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (318176144478422038691630120543/1712653973615039062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (78431703814209615489858719/856326986807519531250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (17/500:ℝ) delta 5-highFee)=
      (4949341613633426750802939167745609/761179543828906250000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (688574078601801022616773904698639/6850615894460156250000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (318176144478422038691630120543/1712653973615039062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (78431703814209615489858719/856326986807519531250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_lo_6 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (17/500:ℝ) delta 6 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (40213682087752988615302847433/6089436350631250000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (293669602659630719368237564171/2740246357784062500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (542539885343738116542180461/2740246357784062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (132900174432296656448297/1370123178892031250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (17/500:ℝ) delta 6-highFee)=
      (40213682087752988615302847433/6089436350631250000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (293669602659630719368237564171/2740246357784062500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (542539885343738116542180461/2740246357784062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (132900174432296656448297/1370123178892031250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem unmarked_A_lo (delta : ℝ) (hL : (7/10:ℝ)≤delta) (hU : delta≤(3/4:ℝ)) :
    highFee ≤ highBase .A (17/500:ℝ) delta := by
  have hl : 0≤delta-(7/10:ℝ) := by linarith
  have hu : 0≤(3/4:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (67823668648506491773/4629937500000000000:ℝ)*(delta-(7/10:ℝ))^0*((3/4:ℝ)-delta)^2+
      (67050954210974992871/1234650000000000000:ℝ)*(delta-(7/10:ℝ))^1*((3/4:ℝ)-delta)^1+
      (61384550137208830591/1481580000000000000:ℝ)*(delta-(7/10:ℝ))^2*((3/4:ℝ)-delta)^0 := by positivity
  have hid : (5-2*delta)*(highBase .A (17/500:ℝ) delta-highFee)=
      (67823668648506491773/4629937500000000000:ℝ)*(delta-(7/10:ℝ))^0*((3/4:ℝ)-delta)^2+
      (67050954210974992871/1234650000000000000:ℝ)*(delta-(7/10:ℝ))^1*((3/4:ℝ)-delta)^1+
      (61384550137208830591/1481580000000000000:ℝ)*(delta-(7/10:ℝ))^2*((3/4:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < 5-2*delta := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_hi_0 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (1/25:ℝ) delta 0 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (10871624910305908175246429094507/115699290661993750000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (793916048457611530136871558889/2082587231915887500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (1005081627319267785128024807/2082587231915887500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (203012677337770952615411/1041293615957943750:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (1/25:ℝ) delta 0-highFee)=
      (10871624910305908175246429094507/115699290661993750000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (793916048457611530136871558889/2082587231915887500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (1005081627319267785128024807/2082587231915887500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (203012677337770952615411/1041293615957943750:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_hi_1 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (1/25:ℝ) delta 1 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (462943929982925610717330909659/18268309051893750000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (27152136716653368673379555731/109609854311362500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (45801661187736807753580253/109609854311362500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (10691765799921530663969/54804927155681250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (1/25:ℝ) delta 1-highFee)=
      (462943929982925610717330909659/18268309051893750000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (27152136716653368673379555731/109609854311362500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (45801661187736807753580253/109609854311362500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (10691765799921530663969/54804927155681250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_hi_2 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (1/25:ℝ) delta 2 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (60696787156416240549715636553/6089436350631250000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (12401436197311772039303555731/109609854311362500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (21790901904626753655580253/109609854311362500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (5221280221067696663969/54804927155681250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (1/25:ℝ) delta 2-highFee)=
      (60696787156416240549715636553/6089436350631250000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (12401436197311772039303555731/109609854311362500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (21790901904626753655580253/109609854311362500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (5221280221067696663969/54804927155681250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_hi_3 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (1/25:ℝ) delta 3 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (1439889988353108282887166662359/2283538631486718750000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (575219485894310657839259538445963/6850615894460156250000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (292503826160598177553794003431/1712653973615039062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (74062790475221276885356823/856326986807519531250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (1/25:ℝ) delta 3-highFee)=
      (1439889988353108282887166662359/2283538631486718750000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (575219485894310657839259538445963/6850615894460156250000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (292503826160598177553794003431/1712653973615039062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (74062790475221276885356823/856326986807519531250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_hi_4 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (1/25:ℝ) delta 4 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (45739308992448986094609938548336231/4567077262973437500000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (1445291385359176108036780213701167/13701231788920312500000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (158299600749503460398138964751/856326986807519531250000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (38186116667661011086650508/428163493403759765625:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (1/25:ℝ) delta 4-highFee)=
      (45739308992448986094609938548336231/4567077262973437500000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (1445291385359176108036780213701167/13701231788920312500000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (158299600749503460398138964751/856326986807519531250000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (38186116667661011086650508/428163493403759765625:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_hi_5 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (1/25:ℝ) delta 5 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (73199468371170632962995155636983/1522359087657812500000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (1045550832483825918802354824218093/13701231788920312500000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (8394380793744127265050952494/53520436675469970703125:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (34426260178180269342071107/428163493403759765625:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (1/25:ℝ) delta 5-highFee)=
      (73199468371170632962995155636983/1522359087657812500000000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (1045550832483825918802354824218093/13701231788920312500000000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (8394380793744127265050952494/53520436675469970703125:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (34426260178180269342071107/428163493403759765625:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_A_hi_6 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .A (1/25:ℝ) delta 6 := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (893925574724975505127049833/6089436350631250000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (226824952051206702555981545251/2740246357784062500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (462286989077718505391719241/2740246357784062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (117360139771202060709857/1370123178892031250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .A (1/25:ℝ) delta 6-highFee)=
      (893925574724975505127049833/6089436350631250000000000:ℝ)*(delta-(6509/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (226824952051206702555981545251/2740246357784062500000000:ℝ)*(delta-(6509/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (462286989077718505391719241/2740246357784062500000:ℝ)*(delta-(6509/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (117360139771202060709857/1370123178892031250:ℝ)*(delta-(6509/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem unmarked_A_hi (delta : ℝ) (hL : (7/10:ℝ)≤delta) (hU : delta≤(3/4:ℝ)) :
    highFee ≤ highBase .A (1/25:ℝ) delta := by
  have hl : 0≤delta-(7/10:ℝ) := by linarith
  have hu : 0≤(3/4:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (57030493597492691773/4629937500000000000:ℝ)*(delta-(7/10:ℝ))^0*((3/4:ℝ)-delta)^2+
      (59693192842757392871/1234650000000000000:ℝ)*(delta-(7/10:ℝ))^1*((3/4:ℝ)-delta)^1+
      (55959340315364230591/1481580000000000000:ℝ)*(delta-(7/10:ℝ))^2*((3/4:ℝ)-delta)^0 := by positivity
  have hid : (5-2*delta)*(highBase .A (1/25:ℝ) delta-highFee)=
      (57030493597492691773/4629937500000000000:ℝ)*(delta-(7/10:ℝ))^0*((3/4:ℝ)-delta)^2+
      (59693192842757392871/1234650000000000000:ℝ)*(delta-(7/10:ℝ))^1*((3/4:ℝ)-delta)^1+
      (55959340315364230591/1481580000000000000:ℝ)*(delta-(7/10:ℝ))^2*((3/4:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < 5-2*delta := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem slope_A_0 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(3/4:ℝ)) :
    2*SourcePlane.rootCutoff .A*(6*rho delta-1) ≤ (delta-3/19) := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(3/4:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (3366809090/18659539:ℝ)*(delta-(6509/10000:ℝ))^0*((3/4:ℝ)-delta)^2+
      (7297168168/18659539:ℝ)*(delta-(6509/10000:ℝ))^1*((3/4:ℝ)-delta)^1+
      (3893040000/18659539:ℝ)*(delta-(6509/10000:ℝ))^2*((3/4:ℝ)-delta)^0 := by positivity
  have hid : (5-2*delta)*((delta-3/19)-2*SourcePlane.rootCutoff .A*(6*rho delta-1))=
      (3366809090/18659539:ℝ)*(delta-(6509/10000:ℝ))^0*((3/4:ℝ)-delta)^2+
      (7297168168/18659539:ℝ)*(delta-(6509/10000:ℝ))^1*((3/4:ℝ)-delta)^1+
      (3893040000/18659539:ℝ)*(delta-(6509/10000:ℝ))^2*((3/4:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < 5-2*delta := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem slope_A_1 (delta : ℝ) (hL : (6509/10000:ℝ)≤delta) (hU : delta≤(3/4:ℝ)) :
    2*SourcePlane.rootCutoff .A*(6*rho delta-1) ≤ (delta-4*rho delta+5/4) := by
  have hl : 0≤delta-(6509/10000:ℝ) := by linarith
  have hu : 0≤(3/4:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (259364330/2946243:ℝ)*(delta-(6509/10000:ℝ))^0*((3/4:ℝ)-delta)^2+
      (1158236816/2946243:ℝ)*(delta-(6509/10000:ℝ))^1*((3/4:ℝ)-delta)^1+
      (297660000/982081:ℝ)*(delta-(6509/10000:ℝ))^2*((3/4:ℝ)-delta)^0 := by positivity
  have hid : (5-2*delta)*((delta-4*rho delta+5/4)-2*SourcePlane.rootCutoff .A*(6*rho delta-1))=
      (259364330/2946243:ℝ)*(delta-(6509/10000:ℝ))^0*((3/4:ℝ)-delta)^2+
      (1158236816/2946243:ℝ)*(delta-(6509/10000:ℝ))^1*((3/4:ℝ)-delta)^1+
      (297660000/982081:ℝ)*(delta-(6509/10000:ℝ))^2*((3/4:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < 5-2*delta := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.channel_A_lo_3
#print axioms OAI.SevenEighths.TargetHigh830.unmarked_A_lo
#print axioms OAI.SevenEighths.TargetHigh830.slope_A_1
