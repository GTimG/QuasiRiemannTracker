/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.DirectPairBinding00
import Candidate.C092.transport.DirectPairBinding01
import Candidate.C092.transport.DirectPairBinding02
import Candidate.C092.transport.DirectPairBinding03
import Candidate.C092.transport.DirectPairBinding04
import Candidate.C092.transport.DirectPairBinding05
import Candidate.C092.transport.DirectPairBinding06
import Candidate.C092.transport.DirectPairBinding07
import Candidate.C092.transport.DirectPairBinding08
import Candidate.C092.transport.DirectPairBinding09
import Candidate.C092.transport.DirectPairBinding10
import Candidate.C092.transport.DirectPairBinding11
import Candidate.C092.transport.DirectPairBinding12
import Candidate.C092.transport.DirectPairBinding13
import Candidate.C092.transport.DirectPairBinding14
import Candidate.C092.transport.DirectPairBinding15
import Candidate.C092.transport.DirectPairBinding16
import Candidate.C092.transport.DirectPairBinding17
import Candidate.C092.transport.DirectPairBinding18
import Candidate.C092.transport.DirectPairBinding19
import Candidate.C092.transport.DirectPairBinding20
import Candidate.C092.transport.DirectPairBinding21
import Candidate.C092.transport.DirectPairBinding22
import Candidate.C092.transport.DirectPairBinding23
import Candidate.C092.transport.DirectPairBinding24
import Candidate.C092.transport.DirectPairBinding25
import Candidate.C092.transport.DirectPairBinding26
import Candidate.C092.transport.DirectPairBinding27
import Candidate.C092.transport.DirectPairBinding28
import Candidate.C092.transport.DirectPairBinding29
import Candidate.C092.transport.DirectPairBinding30
import Candidate.C092.transport.DirectPairBinding31
import Candidate.C092.transport.DirectPairBinding32
import Candidate.C092.transport.DirectPairBinding33
import Candidate.C092.transport.DirectPairBinding34
import Candidate.C092.transport.DirectPairBinding35
import Candidate.C092.transport.DirectPairBinding36
import Candidate.C092.transport.DirectPairBinding37
import Candidate.C092.transport.DirectPairBinding38
import Candidate.C092.transport.DirectPairBinding39
import Candidate.C092.transport.DirectPairBinding40
import Candidate.C092.transport.DirectPairBinding41
import Candidate.C092.transport.DirectPairBinding42
import Candidate.C092.transport.DirectPairBinding43
import Candidate.C092.transport.DirectPairBinding44
import Candidate.C092.transport.DirectPairBinding45
import Candidate.C092.transport.DirectPairBinding46
import Candidate.C092.transport.DirectPairBinding47
import Candidate.C092.transport.DirectPairBinding48
import Candidate.C092.transport.DirectPairBinding49
import Candidate.C092.transport.DirectPairBinding50
import Candidate.C092.transport.DirectPairBinding51
import Candidate.C092.transport.DirectPairBinding52
import Candidate.C092.transport.DirectPairBinding53
import Candidate.C092.transport.DirectPairBinding54
import Candidate.C092.transport.DirectPairBinding55
import Candidate.C092.transport.DirectPairBinding56
set_option autoImplicit false
namespace QRH.Cycle092.Direct
noncomputable section
open QRH.PhysicalCertificate QRH.Coverage QRH.Cycle090

theorem actual_initial_paired_check (index : Fin 57) :
    pairedTreeCheck (originalAt index).edge (initialAt index) = true := by
  fin_cases index
  · exact pair_initialTree00
  · exact pair_initialTree01
  · exact pair_initialTree02
  · exact pair_initialTree03
  · exact pair_initialTree04
  · exact pair_initialTree05
  · exact pair_initialTree06
  · exact pair_initialTree07
  · exact pair_initialTree08
  · exact pair_initialTree09
  · exact pair_initialTree10
  · exact pair_initialTree11
  · exact pair_initialTree12
  · exact pair_initialTree13
  · exact pair_initialTree14
  · exact pair_initialTree15
  · exact pair_initialTree16
  · exact pair_initialTree17
  · exact pair_initialTree18
  · exact pair_initialTree19
  · exact pair_initialTree20
  · exact pair_initialTree21
  · exact pair_initialTree22
  · exact pair_initialTree23
  · exact pair_initialTree24
  · exact pair_initialTree25
  · exact pair_initialTree26
  · exact pair_initialTree27
  · exact pair_initialTree28
  · exact pair_initialTree29
  · exact pair_initialTree30
  · exact pair_initialTree31
  · exact pair_initialTree32
  · exact pair_initialTree33
  · exact pair_initialTree34
  · exact pair_initialTree35
  · exact pair_initialTree36
  · exact pair_initialTree37
  · exact pair_initialTree38
  · exact pair_initialTree39
  · exact pair_initialTree40
  · exact pair_initialTree41
  · exact pair_initialTree42
  · exact pair_initialTree43
  · exact pair_initialTree44
  · exact pair_initialTree45
  · exact pair_initialTree46
  · exact pair_initialTree47
  · exact pair_initialTree48
  · exact pair_initialTree49
  · exact pair_initialTree50
  · exact pair_initialTree51
  · exact pair_initialTree52
  · exact pair_initialTree53
  · exact pair_initialTree54
  · exact pair_initialTree55
  · exact pair_initialTree56

/-- Every actual E49 terminal is paid at every real point of its original closed box. -/
theorem all_actual_E49_price {index : Fin 57} {leaf : DirectLeaf}
    (hm : leaf ∈ (initialAt index).directRecords) (hr : leaf.route = "E49_top")
    {h g₀ g₁ : ℝ} {point : Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : leaf.box.Contains point)
    (hg₀ : 5805911 / 100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913 / 100000000)
    (hg₁ : 3799809 / 50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981 / 5000000) :
    (originalAt index).edge = 3 ∧
      1 / 125000000 ≤ theta - Physical.price h point.1 point.2 g₀ g₁ h := by
  obtain ⟨he,box,hbox,hin⟩ := pairedTreeCheck_sound _ _ (actual_initial_paired_check index) hm hr
  exact ⟨he, certified_paired_top hbox hh hh' (Box.contains_of_included hin hp) hg₀ hg₀' hg₁ hg₁'⟩

/-- All actual E49 direct terminals retain strict surplus through the padded
support, at the actual algebraic contact. The original literal Q1 price is used. -/
theorem all_actual_E49_padded {index : Fin 57} {leaf : DirectLeaf}
    (hm : leaf ∈ (initialAt index).directRecords) (hr : leaf.route = "E49_top")
    {h x D : ℝ} {point : Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : leaf.box.Contains point)
    (hx : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval x)
    (hDh : D ≤ h + rowPad) :
    0 < theta - Physical.price h point.1 point.2
      (QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue x))
      (QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue x)) D -
      paddingDebit - 1 / 100000000000000 := by
  obtain ⟨_,box,hbox,hin⟩ := pairedTreeCheck_sound _ _ (actual_initial_paired_check index) hm hr
  have hpbox := Box.contains_of_included hin hp
  have hc := List.all_eq_true.mp pairedBoxes_checked box hbox
  simp only [Physical.exteriorBoxCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hd0 : (0 : ℝ) ≤ (box.uLo : ℝ) := Rat.cast_nonneg.mpr hc.1.1
  have hd1 : (box.uHi : ℝ) ≤ (1/2 : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le.mpr hc.1.2.2.1 : (box.uHi : ℝ) ≤ ((1/2 : ℚ) : ℝ))
  have hp0 : (0 : ℝ) ≤ (box.vLo : ℝ) := Rat.cast_nonneg.mpr hc.1.2.2.2.1
  have hp1 : (box.vHi : ℝ) ≤ (1/2 : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le.mpr hc.1.2.2.2.2.2 : (box.vHi : ℝ) ≤ ((1/2 : ℚ) : ℝ))
  have hb := Physical.actual_contact_bounds hx
  have ht := (all_actual_E49_price hm hr hh hh' hp hb.1 hb.2.1 hb.2.2.1 hb.2.2.2).2
  have hs := sourceCost_le_rowPad
  have hrp := rowPad_small
  by_cases hle : D ≤ h
  · have hmono := Physical.price_mono_conductor (hd0.trans hpbox.1) (hpbox.2.1.trans hd1)
      (hp0.trans hpbox.2.2.1) (hpbox.2.2.2.trans hp1)
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hle
    dsimp [paddingDebit]
    linarith
  · have hinc := Physical.price_increment_le (hd0.trans hpbox.1) (hpbox.2.1.trans hd1)
      (hp0.trans hpbox.2.2.1) (hpbox.2.2.2.trans hp1)
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 (le_of_not_ge hle)
    dsimp [paddingDebit]
    linarith

end
end QRH.Cycle092.Direct
#print axioms QRH.Cycle092.Direct.all_actual_E49_price

#print axioms QRH.Cycle092.Direct.all_actual_E49_padded
