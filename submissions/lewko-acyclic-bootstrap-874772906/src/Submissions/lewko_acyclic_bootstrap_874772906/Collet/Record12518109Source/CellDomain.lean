/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.DomainEndpoints
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Schedule
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission

def cellFace (c : Cell) : SourceFace :=
  ⟨c.B,c.L,c.plainLo,c.plainHi,c.lo,c.hi⟩
def priorFace (c : Cell) : SourceFace :=
  ⟨c.priorB,c.priorL,c.priorPlainLo,c.priorPlainHi,c.priorLo,c.priorHi⟩
def rawCells : Fin 15→Cell :=
  ![cell0,cell1,cell2,cell3,cell4,cell5,cell6,cell7,cell8,cell9,cell10,cell11,cell12,cell13,cell14]

theorem raw_cell_prior_bounds (i : Fin 15) :
    let c:=rawCells i
    0≤K ∧ 0<c.priorL ∧ 0≤c.priorPlainHi ∧ 0≤c.priorB ∧
      0≤c.priorB-c.priorL*c.priorLo ∧
      0≤c.priorB-c.priorL*c.priorHi ∧
      0≤1-K*c.priorLo ∧
      1-c.priorPlainLo-K*c.priorB/c.priorL≤0 ∧
      1≤c.priorL ∧ 0≤c.cut := by
  fin_cases i <;> norm_num [rawCells,K,incumbent,
    cell0,cell1,cell2,cell3,cell4,cell5,cell6,cell7,cell8,cell9,
    cell10,cell11,cell12,cell13,cell14]

theorem raw_cell_domains (i : Fin 15) {b : ℝ}
    (hb : b ∈ Set.Icc (rawCells i).lo (rawCells i).hi)
    (j : Fin 9) (upper : Bool) : 0<domainBranch (rawCells i) j upper b := by
  fin_cases i
  · exact cell0_all_domains (by simpa [rawCells,cell0] using hb) j upper
  · exact cell1_all_domains (by simpa [rawCells,cell1] using hb) j upper
  · exact cell2_all_domains (by simpa [rawCells,cell2] using hb) j upper
  · exact cell3_all_domains (by simpa [rawCells,cell3] using hb) j upper
  · exact cell4_all_domains (by simpa [rawCells,cell4] using hb) j upper
  · exact cell5_all_domains (by simpa [rawCells,cell5] using hb) j upper
  · exact cell6_all_domains (by simpa [rawCells,cell6] using hb) j upper
  · exact cell7_all_domains (by simpa [rawCells,cell7] using hb) j upper
  · exact cell8_all_domains (by simpa [rawCells,cell8] using hb) j upper
  · exact cell9_all_domains (by simpa [rawCells,cell9] using hb) j upper
  · exact cell10_all_domains (by simpa [rawCells,cell10] using hb) j upper
  · exact cell11_all_domains (by simpa [rawCells,cell11] using hb) j upper
  · exact cell12_all_domains (by simpa [rawCells,cell12] using hb) j upper
  · exact cell13_all_domains (by simpa [rawCells,cell13] using hb) j upper
  · exact cell14_all_domains (by simpa [rawCells,cell14] using hb) j upper

/-- The certified padded endpoint inequalities give the previous-face and
natural downward domain for the actual first-geometry quotient. -/
theorem raw_first_cap_admission {c : Cell} {b P Q m₁ m₂ : ℝ}
    (hK : 0≤K) (hL : 0<c.priorL) (hu : 0≤c.priorPlainHi)
    (hBLo : 0≤c.priorB-c.priorL*c.priorLo)
    (hBHi : 0≤c.priorB-c.priorL*c.priorHi)
    (hNLo : 0≤1-K*c.priorLo)
    (hCoeff : 1-c.priorPlainLo-K*c.priorB/c.priorL≤0)
    (hdom : ∀j : Fin 9,∀upper : Bool,0<domainBranch c j upper b)
    (hQlo : radiusLo c b≤Q) (hQhi : Q≤radiusHi c b)
    (hPlo : plainCap c b-c.cut≤P) (hPhi : P≤plainCap c b)
    (hP : m₁+m₂=P) (hm₁ : m₁≤c.plainHi) (hm₂ : m₂≤c.plainHi) :
    (priorFace c).slotLo*Q≤firstSlotCap (priorFace c) P Q ∧
      firstSlotCap (priorFace c) P Q≤(priorFace c).slotHi*Q ∧
      DownwardCaps (priorFace c) K m₁ m₂ (firstSlotCap (priorFace c) P Q) Q := by
  have h1:=hdom ⟨1,by decide⟩ false
  have h2:=hdom ⟨2,by decide⟩ true
  have h4:=hdom ⟨4,by decide⟩ false
  have h5:=hdom ⟨5,by decide⟩ false
  have h6:=hdom ⟨6,by decide⟩ true
  have hfee : 0<lowFee := by norm_num [lowFee]
  norm_num [domainBranch] at h1 h2 h4 h5 h6
  apply first_cap_admission_endpoints hK hL hu hQlo hQhi hPlo hPhi hP hm₁ hm₂
    hBLo hBHi hNLo hCoeff
  · exact (by dsimp only [priorFace]; linarith only [h1,hfee])
  · exact (by dsimp only [priorFace]; linarith only [h2,hfee])
  · exact (by dsimp only [priorFace]; linarith only [h4,hfee])
  · exact (by dsimp only [priorFace]; linarith only [h5,hfee])
  · exact (by dsimp only [priorFace]; linarith only [h6,hfee])

theorem raw_first_cap_le_width {c : Cell} {b P Q : ℝ}
    (hL : 0<c.priorL) (hL1 : 1≤c.priorL) (hB : 0≤c.priorB)
    (hcut : 0≤c.cut) (hdom : 0<domainBranch c 3 true b)
    (hQhi : Q≤radiusHi c b) (hPlo : plainCap c b-c.cut≤P) :
    firstSlotCap (priorFace c) P Q≤b := by
  have hmul:=mul_le_mul_of_nonneg_left hQhi hB
  have hc:=mul_le_mul_of_nonneg_right hL1 hcut
  have hfee : 0<lowFee := by norm_num [lowFee]
  dsimp only [firstSlotCap,priorFace]
  apply (div_le_iff₀ hL).mpr
  norm_num [domainBranch] at hdom
  nlinarith only [hmul,hc,hfee,hdom,hPlo]

theorem certified_raw_first_cap (i : Fin 15) {b P Q m₁ m₂ : ℝ}
    (hb : b ∈ Set.Icc (rawCells i).lo (rawCells i).hi)
    (hQlo : radiusLo (rawCells i) b≤Q) (hQhi : Q≤radiusHi (rawCells i) b)
    (hPlo : plainCap (rawCells i) b-(rawCells i).cut≤P)
    (hPhi : P≤plainCap (rawCells i) b)
    (hP : m₁+m₂=P) (hm₁ : m₁≤(rawCells i).plainHi) (hm₂ : m₂≤(rawCells i).plainHi) :
    let f:=priorFace (rawCells i)
    f.slotLo*Q≤firstSlotCap f P Q ∧ firstSlotCap f P Q≤f.slotHi*Q ∧
      DownwardCaps f K m₁ m₂ (firstSlotCap f P Q) Q ∧ firstSlotCap f P Q≤b := by
  obtain ⟨hK,hL,hu,hB,hBLo,hBHi,hNLo,hCoeff,hL1,hcut⟩:=raw_cell_prior_bounds i
  have hdom:=raw_cell_domains i hb
  obtain ⟨hlo,hhi,hcaps⟩:=raw_first_cap_admission hK hL hu hBLo hBHi hNLo hCoeff
    hdom hQlo hQhi hPlo hPhi hP hm₁ hm₂
  exact ⟨hlo,hhi,hcaps,raw_first_cap_le_width hL hL1 hB hcut (hdom 3 true) hQhi hPlo⟩
end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.certified_raw_first_cap
