/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual checked response/cutoff tables at finitely many earlier length labels,
and one genuine inverse rectangle bank paid from their common positive fee.
All these choices precede Slot, arithmetic data and live row families. -/
import Candidate.C092.transport.StrongPairRegularTerminalDispatch
import Candidate.C092.transport.MediumInversePriceSourceBank

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.MediumInversePrice
open Qrh.MarkedAnchor.Interface.Contract

/-- The cutoffs are genuine entries of the recorded certificate cell.
The actual medium zero lower endpoint is max(eLower,nuGrid). -/
structure TerminalResponseTable (y step : ℝ) (cell : Cell) where
  Je : ℕ
  Jν : ℕ
  egrid : Fin Je→ℝ
  νgrid : Fin Jν→ℝ
  eBounds : ∀ ie,(cell.threshold:ℝ) ≤ egrid ie ∧ egrid ie ≤ (responseUpper:ℝ)
  νBounds : ∀ iv,0 ≤ νgrid iv ∧ νgrid iv ≤ 3/4
  cutoff : Fin Je×Fin Jν→Cutoff
  recorded : ∀ j,∃ p∈cell.cutoffs.zipIdx,p.1=cutoff j
  guard : ∀ j,CutoffGuard cell.upper (cutoff j)
  paid : ∀ j,PaidWithBand y (egrid j.1) (max (egrid j.1) (νgrid j.2)) (cutoff j)
  inverseCap : ∀ j,2*y/(H:ℝ) ≤ ((cutoff j).inverse:ℝ)
  ordinaryCap : ∀ j,y/(H:ℝ) ≤ ((cutoff j).ordinary:ℝ)
  sumCap : ∀ j,y < (H:ℝ)*(((cutoff j).inverse:ℝ)+((cutoff j).ordinary:ℝ))/2
  cover : ∀ e ν : ℝ,(cell.threshold:ℝ) ≤ e → e ≤ (responseUpper:ℝ) → e ≤ ν → ν ≤ 3/4 →
    ∃ j : Fin Je×Fin Jν,egrid j.1 ≤ e ∧ e < egrid j.1+step ∧
      max (egrid j.1) (νgrid j.2) ≤ ν ∧ ν < max (egrid j.1) (νgrid j.2)+step ∧
      0 ≤ egrid j.1 ∧ egrid j.1 ≤ max (egrid j.1) (νgrid j.2) ∧
      max (egrid j.1) (νgrid j.2) ≤ 3/4

/-- The genuine ceiling source gives response<=nu+price. Use max(response,nu)
only to select the stored cell; all analytic comparisons retain the actual nu.
Thus the downward discrepancy is explicitly bounded by price. -/
theorem terminal_table_approx_cover {y step price e ν : ℝ} {cell : Cell}
    (table : TerminalResponseTable y step cell) (hprice : 0 ≤ price)
    (he0 : (cell.threshold:ℝ) ≤ e) (he1 : e ≤ (responseUpper:ℝ))
    (hceiling : e ≤ ν+price) (hν : ν ≤ 3/4) :
    ∃ j : Fin table.Je×Fin table.Jν,
      table.egrid j.1 ≤ e ∧ e < table.egrid j.1+step ∧
      max (table.egrid j.1) (table.νgrid j.2) ≤ ν+price ∧
      ν < max (table.egrid j.1) (table.νgrid j.2)+step ∧
      0 ≤ table.egrid j.1 ∧ table.egrid j.1 ≤ max (table.egrid j.1) (table.νgrid j.2) ∧
      max (table.egrid j.1) (table.νgrid j.2) ≤ 3/4 := by
  have heν : max e ν ≤ 3/4 := max_le (he1.trans (by norm_num [responseUpper])) hν
  obtain ⟨j,h0,h1,h2,h3,h4,h5,h6⟩ := table.cover e (max e ν) he0 he1 (le_max_left _ _) heν
  have hm : max e ν ≤ ν+price := max_le hceiling (by linarith)
  exact ⟨j,h0,h1,h2.trans hm,(le_max_right e ν).trans_lt h3,h4,h5,h6⟩

/-- Each cell is chosen before the window size, for every member of the
finite genuine length bank. No choice depends on Slot/ray or a live row. -/
theorem terminal_finite_checked_tables {Key : Type*} [Fintype Key]
    (y : Key→ℝ) (hy0 : ∀ k,(369/1000:ℝ) ≤ y k) (hy1 : ∀ k,y k ≤ (243/625:ℝ)) :
    ∃ cells : Key→Cell,
      (∀ k,cells k∈sourceCells ∧ ((cells k).lower:ℝ) ≤ y k ∧ y k ≤ ((cells k).upper:ℝ) ∧
        0 < ((cells k).threshold:ℝ) ∧ ((cells k).threshold:ℝ) ≤ (responseUpper:ℝ) ∧
        ((cells k).threshold:ℝ)*max 0 (lowBracketAt (y k)) < (u-rho:ℚ)) ∧
      ∀ step : ℝ,0 < step → Nonempty (∀ k,TerminalResponseTable (y k) step (cells k)) := by
  have h (k : Key) := terminal_checked_windows (hy0 k) (hy1 k)
  choose cells hcells hyl hyu ht0 ht1 hlow htable using h
  refine ⟨cells,fun k=>⟨hcells k,hyl k,hyu k,ht0 k,ht1 k,hlow k⟩,?_⟩
  intro step hs
  have ht (k : Key) : Nonempty (TerminalResponseTable (y k) step (cells k)) := by
    obtain ⟨Je,Jν,eg,ng,heg,hng,hcut,hcover⟩ := htable k step hs
    have hp (j : Fin Je×Fin Jν) := hcut j.1 j.2
    choose p hp hg hpaid hi ho hsum using hp
    refine ⟨{
      Je := Je
      Jν := Jν
      egrid := eg
      νgrid := ng
      eBounds := heg
      νBounds := hng
      cutoff := fun j => (p j).1
      recorded := fun j => ⟨p j,hp j,rfl⟩
      guard := hg
      paid := hpaid
      inverseCap := hi
      ordinaryCap := ho
      sumCap := hsum
      cover := ?_ }⟩
    intro e ν he he' hν hν'
    obtain ⟨ie,iv,hcover⟩ := hcover e ν he he' hν hν'
    exact ⟨(ie,iv),hcover⟩
  exact ⟨fun k=>Classical.choice (ht k)⟩

/-- The common decrement is chosen AFTER the finite scalar fees but BEFORE
selecting a rectangle. Every selected rectangle is an authentic source.
This avoids an opaque rho-before-fee existential cycle. -/
theorem terminal_uniform_genuine_inverse_bank {Key : Type*} [Fintype Key]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (fee : Key→ℝ) (hfee : ∀ k,0 < fee k) :
    ∃ ζ : ℝ,0 < ζ ∧ (∀ k,ζ ≤ fee k/2) ∧
    ∃ δ : ℝ,0 < δ ∧ δ ≤ 1/1000 ∧ 3*δ ≤ ζ ∧
    ∃ J : ℕ,∃ bank : Fin J→AnchorRect,
      (∀ j,UniformInverseRectSource canonicalFamily (bank j)) ∧
      ∀ r : ℝ,367/500 ≤ r → r ≤ 1 →
        inverseQuota r ≤ ζ ∨ (0 ≤ inverseQuota r-ζ → ∃ j,(bank j).Admissible r (inverseQuota r-ζ) 1) := by
  let fees : Finset ℝ := insert 1 (Finset.univ.image fee)
  have hne : fees.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  let f := fees.min' hne
  have hf : 0 < f := by
    have hm : f∈fees := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hm with hm|hm
    · rw [hm];norm_num
    · obtain ⟨k,_,heq⟩ := Finset.mem_image.mp hm
      rw [←heq]
      exact hfee k
  have hfk (k : Key) : f ≤ fee k := Finset.min'_le fees (fee k)
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩))
  let ζ := f/2
  have hζ : 0 < ζ := by dsimp [ζ];positivity
  obtain ⟨δ,hδ,hδsmall,hδζ,J,bank,hsource,hcover⟩ := finite_genuine_inverse_sources hβ hζ
  exact ⟨ζ,hζ,fun k=>by dsimp [ζ];linarith [hfk k],δ,hδ,hδsmall,hδζ,J,bank,hsource,hcover⟩

theorem terminal_positive_mesh_floor {Key : Type*} [Fintype Key]
    (mesh : Key→ℝ) (hm : ∀ k,0 < mesh k) :
    ∃ common : ℝ,0 < common ∧ ∀ k,common ≤ mesh k := by
  let meshes : Finset ℝ := insert 1 (Finset.univ.image mesh)
  have hne : meshes.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨meshes.min' hne,?_,?_⟩
  · have hmem := Finset.min'_mem meshes hne
    rcases Finset.mem_insert.mp hmem with h|h
    · rw [h];norm_num
    · obtain ⟨k,_,heq⟩ := Finset.mem_image.mp h
      rw [←heq]
      exact hm k
  · intro k
    exact Finset.min'_le meshes (mesh k)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩))

#print axioms terminal_finite_checked_tables
#print axioms terminal_table_approx_cover
#print axioms terminal_uniform_genuine_inverse_bank
#print axioms terminal_positive_mesh_floor
end
end QRH.Cycle092.StrongPair
