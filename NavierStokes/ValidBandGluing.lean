import NavierStokes.SpatialCurl

/-!
# A representative on the union of valid open charts

Local formulas are identified only where both charts are valid.  The
chosen representative agrees with every valid chart on an ambient
neighborhood.  No regularity at the boundary of the union is asserted.
-/

noncomputable section

namespace NavierStokes.ValidBandGluing

open Set Filter Function
open scoped Topology ContDiff

variable {ι D E : Type*}

def domain (U : ι → Set D) : Set D := ⋃ i, U i

def Compatible (U : ι → Set D) (f : ι → D → E) : Prop :=
  ∀ i j, EqOn (f i) (f j) (U i ∩ U j)

/-- Choose a chart only at points covered by at least one valid chart.
The value outside the valid union is the stated zero totalization. -/
noncomputable def representative [Zero E] (U : ι → Set D) (f : ι → D → E) (x : D) : E := by
  classical
  exact if h : ∃ i, x ∈ U i then f (Classical.choose h) x else 0

theorem mem_domain_iff {U : ι → Set D} {x : D} : x ∈ domain U ↔ ∃ i, x ∈ U i :=
  mem_iUnion

theorem representative_zero [Zero E] {U : ι → Set D} {f : ι → D → E}
    {x : D} (hx : x ∉ domain U) : representative U f x = 0 := by
  have hn : ¬ ∃ i, x ∈ U i := fun h => hx (mem_domain_iff.mpr h)
  simp only [representative, dite_eq_right hn]

theorem representative_eq_of_mem [Zero E] {U : ι → Set D} {f : ι → D → E}
    (hf : Compatible U f) {i : ι} {x : D} (hx : x ∈ U i) :
    representative U f x = f i x := by
  classical
  have h : ∃ j, x ∈ U j := ⟨i, hx⟩
  simp only [representative, dite_eq_left h]
  exact hf (Classical.choose h) i ⟨Classical.choose_spec h, hx⟩



section Topology

variable [TopologicalSpace D]

theorem domain_open {U : ι → Set D} (hU : ∀ i, IsOpen (U i)) : IsOpen (domain U) :=
  isOpen_iUnion hU

theorem representative_germ [Zero E] {U : ι → Set D} {f : ι → D → E}
    (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f) {i : ι} {x : D} (hx : x ∈ U i) :
    representative U f =ᶠ[𝓝 x] f i :=
  eventually_of_mem ((hU i).mem_nhds hx) (fun _ hy => representative_eq_of_mem hf hy)



end Topology

section Derivatives

variable [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {U : ι → Set D} {f : ι → D → E}

theorem representative_contDiffAt {n : WithTop ℕ∞}
    (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f) {i : ι} {x : D} (hx : x ∈ U i)
    (hs : ContDiffOn ℝ n (f i) (U i)) : ContDiffAt ℝ n (representative U f) x :=
  (hs.contDiffAt ((hU i).mem_nhds hx)).congr_of_eventuallyEq (representative_germ hU hf hx)

theorem representative_contDiffOn {n : WithTop ℕ∞}
    (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    (hs : ∀ i, ContDiffOn ℝ n (f i) (U i)) : ContDiffOn ℝ n (representative U f) (domain U) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_domain_iff.mp hx
  exact (representative_contDiffAt hU hf hi (hs i)).contDiffWithinAt


/-- The actual multilinear derivative tensors agree as functions near
each valid point. No differentiability premise is needed for germ locality. -/
theorem representative_iteratedFDeriv_germ (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    {i : ι} {x : D} (hx : x ∈ U i) (m : ℕ) :
    iteratedFDeriv ℝ m (representative U f) =ᶠ[𝓝 x] iteratedFDeriv ℝ m (f i) := by
  have he : representative U f =ᶠ[𝓝[univ] x] f i := by
    simpa only [nhdsWithin_univ] using representative_germ hU hf hx
  simpa only [nhdsWithin_univ, iteratedFDerivWithin_univ] using
    he.iteratedFDerivWithin (𝕜 := ℝ) m

theorem representative_iteratedFDeriv_eq (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    {i : ι} {x : D} (hx : x ∈ U i) (m : ℕ) :
    iteratedFDeriv ℝ m (representative U f) x = iteratedFDeriv ℝ m (f i) x :=
  (representative_iteratedFDeriv_germ hU hf hx m).self_of_nhds





end Derivatives

section PhysicalCurl

open ProblemStatement




end PhysicalCurl

end NavierStokes.ValidBandGluing
