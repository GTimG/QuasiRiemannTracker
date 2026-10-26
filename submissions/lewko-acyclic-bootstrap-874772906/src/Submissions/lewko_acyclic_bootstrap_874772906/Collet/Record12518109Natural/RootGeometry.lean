/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform scalar admission for all residual sixth-root frequencies and source rays. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.RawGeometryHeight

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open Filter

def RootGeometryAt {Slot : Type} (Z τ δ dmin dmax rmin Rwidth mesh ηslot F dsource : ℝ)
    (I i : ℕ) (slots : Finset Slot) (w : Slot→ℝ) : Prop :=
  (∀q : ℝ,F/2≤q→q≤F→
    dmin≤q+δ ∧q+δ≤dmax ∧2≤Z^(q+δ) ∧2<Z^τ ∧
    (∀s∈slots,w s/(q+δ)≤mesh) ∧
    2*Real.pi*((Z^(q+δ))^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤rawGeometryHeight Z τ I ∧
    (∀s∈slots,rmin≤w s/(q+δ) ∧w s/(q+δ)≤Rwidth) ∧
    (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^(q+δ))^ηslot) ∧
  dmin≤dsource ∧dsource≤dmax ∧2≤Z^dsource ∧
    (∀s∈slots,rmin≤w s/dsource ∧w s/dsource≤Rwidth) ∧
    (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^dsource)^ηslot

theorem eventually_uniform_root_geometry
    (qlo Q τ δ Bmask dmin dmax rmin Rwidth mesh ηslot wmin : ℝ) (I : ℕ)
    (hqlo : 0≤qlo) (hQ : qlo≤Q) (hBmask : 0≤Bmask) (hδ : 0≤δ)
    (hdmin : 0<dmin) (hdlo : dmin≤qlo/2+δ)
    (hdmax : Q+Bmask+δ≤dmax) (hτ : 0<τ)
    (hηslot : 0≤ηslot) (hheight : 2*τ<dmin*ηslot)
    (hwmin : 0≤wmin) (hrmin : rmin≤wmin/dmax) (hmesh : 0≤mesh) (hRwidth : mesh≤Rwidth) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧∀F : ℝ,qlo≤F→F≤Q→∀i : ℕ,i≤I→
      ∀{Slot : Type}(slots : Finset Slot)(w : Slot→ℝ),
      (∀s∈slots,wmin≤w s)→(∀s∈slots,w s≤mesh*dmin)→
      RootGeometryAt Z τ δ dmin dmax rmin Rwidth mesh ηslot F (Q+Bmask+δ) I i slots w := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop (2:ℝ)),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_buffer_height_power dmin τ ηslot I hτ.le hηslot hheight] with Z hZ hbase hT hh
  refine ⟨hZ,?_⟩
  intro F hFlo hFhi i hi Slot slots w hwlo hwhi
  have hds : dmin≤Q+Bmask+δ:=by linarith
  have hdm : 0<dmax:=hdmin.trans_le (hds.trans hdmax)
  have hwidth (d : ℝ)(hd : dmin≤d)(hd' : d≤dmax)(s : Slot)(hs : s∈slots) :
      rmin≤w s/d ∧w s/d≤Rwidth := by
    have hn:=normalized_slot_width hdmin hd hd' hwmin (hwlo s hs) (hwhi s hs)
    exact ⟨hrmin.trans hn.1,hn.2.trans hRwidth⟩
  refine ⟨?_,hds,hdmax,?_,?_,hh.2 _ hds i hi⟩
  · intro q hqlo' hqhi
    have hqd : dmin≤q+δ:=by linarith
    have hqd' : q+δ≤dmax:=by linarith
    refine ⟨hqd,hqd',?_,hT,?_,?_,hwidth _ hqd hqd',hh.2 _ hqd i hi⟩
    · exact hbase.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hqd)
    · intro s hs
      exact (normalized_slot_width hdmin hqd hqd' hwmin (hwlo s hs) (hwhi s hs)).2
    · exact raw_geometry_height_residual hZ.le hτ.le hdm hqd' i I hi
  · exact hbase.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hds)
  · exact hwidth _ hds hdmax

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.eventually_uniform_root_geometry
