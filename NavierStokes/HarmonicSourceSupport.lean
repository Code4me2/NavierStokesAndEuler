import NavierStokes.PeriodizedWaveBounds

/-!
# Support of the actual harmonic residual supplied to a copy solve

The support conclusions below are derived from the literal harmonic
derivatives, convolutions, real projection, and removal of the zero mode.
Only nonzero input harmonics need be localized: a spatially global zero
mode, such as an axisymmetric pressure alias, does not create a new slot.
-/

noncomputable section

namespace NavierStokes.HarmonicSourceSupport

open Set Function Filter HarmonicFields HarmonicResidual HarmonicCalculus
open scoped Topology ContDiff BigOperators ComplexConjugate

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Every nonzero harmonic vanishes outside the specified spatial set.
The zero coefficient is unrestricted. -/
def NonzeroSupported (K : Set D) (c : HarmonicFields.Coefficients D) : Prop :=
  ∀ j : ℤ, j ≠ 0 → ∀ x : D, x ∉ K → c j x = 0

namespace NonzeroSupported

variable {K : Set D} {c d : HarmonicFields.Coefficients D}

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem zero : NonzeroSupported K (0 : HarmonicFields.Coefficients D) := by
  intro j hj x hx
  rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem mono (hc : NonzeroSupported K c) {L : Set D} (hKL : K ⊆ L) :
    NonzeroSupported L c := fun j hj x hx => hc j hj x (fun hk => hx (hKL hk))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem add (hc : NonzeroSupported K c) (hd : NonzeroSupported K d) :
    NonzeroSupported K (c + d) := by
  intro j hj x hx
  change c j x + d j x = 0
  rw [hc j hj x hx, hd j hj x hx, add_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem neg (hc : NonzeroSupported K c) : NonzeroSupported K (-c) := by
  intro j hj x hx
  change -c j x = 0
  rw [hc j hj x hx, neg_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem sub (hc : NonzeroSupported K c) (hd : NonzeroSupported K d) :
    NonzeroSupported K (c - d) := by
  simpa only [sub_eq_add_neg] using hc.add hd.neg

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- In a nonzero convolution mode, at least one input index is nonzero. -/
theorem mul (hc : NonzeroSupported K c) (hd : NonzeroSupported K d) :
    NonzeroSupported K (c * d) := by
  intro j hj x hx
  rw [HarmonicFields.convolution_apply]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    simp only [sub_zero, hd j hj x hx, mul_zero]
  · simp only [hc i hi0 x hx, zero_mul]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem constant (f : D → ℂ) : NonzeroSupported K (constantCoefficient f) := by
  intro j hj x hx
  simp [constantCoefficient, hj]

omit [NormedSpace ℝ D] in
theorem coefficient_germ (hc : NonzeroSupported K c) (hK : IsClosed K)
    {j : ℤ} (hj : j ≠ 0) {x : D} (hx : x ∉ K) :
    c j =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
  exact hc j hj y hy

/-- Actual Fréchet differentiation is local, including when no regularity
of the coefficient is assumed on the other side of the support. -/
theorem differentiate (hc : NonzeroSupported K c) (hK : IsClosed K)
    (V : D → D) (k : ℝ) (Φ : D → ℝ) : NonzeroSupported K (HarmonicFields.differentiate V k Φ c) := by
  intro j hj x hx
  have he := hc.coefficient_germ hK hj hx
  simp only [differentiate_apply, derivativeCoefficient, along, he.fderiv_eq,
    fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, hc j hj x hx, mul_zero, add_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angular (hc : NonzeroSupported K c) (kp : ℤ) :
    NonzeroSupported K (angularDifferentiate kp c) := by
  intro j hj x hx
  simp only [angularDifferentiate_apply, hc j hj x hx, mul_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realProjection (hc : NonzeroSupported K c) : NonzeroSupported K (realCoefficients c) := by
  intro j hj x hx
  simp only [realCoefficients_apply, hc j hj x hx, hc (-j) (neg_ne_zero.mpr hj) x hx,
    map_zero, add_zero, mul_zero]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nonconstant (hc : NonzeroSupported K c) : NonzeroSupported K (HarmonicResidual.nonconstant c) := by
  intro j hj x hx
  simpa only [HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase, Finsupp.erase_ne hj] using hc j hj x hx

omit [NormedSpace ℝ D] in
theorem tsupport (hc : NonzeroSupported K c) (hK : IsClosed K) {j : ℤ} (hj : j ≠ 0) :
    _root_.tsupport (c j) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  exact hx (hc j hj x hn)


end NonzeroSupported

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem rotate_supported {K : Set D} {a : HarmonicResidual.VectorCoefficients D}
    (ha : ∀ i, NonzeroSupported K (a i)) : ∀ i, NonzeroSupported K (rotate a i) := by
  intro i
  fin_cases i
  · exact (ha 1).neg
  · exact ha 0
  · exact NonzeroSupported.zero

theorem scalarLaplacian_supported {K : Set D} (hK : IsClosed K)
    (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {c : HarmonicFields.Coefficients D} (hc : NonzeroSupported K c) :
    NonzeroSupported K (scalarLaplacian g k Φ kp c) :=
  (((hc.differentiate hK g.radial k Φ).differentiate hK g.radial k Φ).add
    ((NonzeroSupported.constant _).mul (hc.differentiate hK g.radial k Φ))).add
      ((NonzeroSupported.constant _).mul ((hc.angular kp).angular kp)) |>.add
        ((hc.differentiate hK g.axial k Φ).differentiate hK g.axial k Φ)

theorem vectorLaplacian_supported {K : Set D} (hK : IsClosed K)
    (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {a : HarmonicResidual.VectorCoefficients D} (ha : ∀ i, NonzeroSupported K (a i)) :
    ∀ i, NonzeroSupported K (vectorLaplacian g k Φ kp a i) := fun i =>
  (scalarLaplacian_supported hK g k Φ kp (ha i)).add
    ((NonzeroSupported.constant _).mul (((NonzeroSupported.constant _).mul
      (rotate_supported (fun j => (ha j).angular kp) i)).add (rotate_supported (rotate_supported ha) i)))

theorem transport_supported {K : Set D} (hK : IsClosed K)
    (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {a b : HarmonicResidual.VectorCoefficients D}
    (ha : ∀ i, NonzeroSupported K (a i)) (hb : ∀ i, NonzeroSupported K (b i)) :
    ∀ i, NonzeroSupported K (HarmonicResidual.transport g k Φ kp a b i) := by
  intro i
  exact (((ha 0).mul ((hb i).differentiate hK g.radial k Φ)).add
    (((ha 1).mul (NonzeroSupported.constant _)).mul
      (((hb i).angular kp).add (rotate_supported hb i)))).add
        ((ha 2).mul ((hb i).differentiate hK g.axial k Φ))

theorem gradient_supported {K : Set D} (hK : IsClosed K)
    (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {p : HarmonicFields.Coefficients D} (hp : NonzeroSupported K p) :
    ∀ i, NonzeroSupported K (HarmonicResidual.gradient g k Φ kp p i) := by
  intro i
  fin_cases i
  · exact hp.differentiate hK g.radial k Φ
  · exact (NonzeroSupported.constant _).mul (hp.angular kp)
  · exact hp.differentiate hK g.axial k Φ

theorem nonlinearResidual_supported {K : Set D} (hK : IsClosed K)
    (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {B a : HarmonicResidual.VectorCoefficients D} {p : HarmonicFields.Coefficients D}
    (hB : ∀ i, NonzeroSupported K (B i)) (ha : ∀ i, NonzeroSupported K (a i))
    (hp : NonzeroSupported K p) :
    ∀ i, NonzeroSupported K (HarmonicResidual.nonlinearResidual g k Φ kp B a p i) := fun i =>
  (((((ha i).differentiate hK g.time k Φ).add (transport_supported hK g k Φ kp hB ha i)).add
    (transport_supported hK g k Φ kp ha hB i)).add (gradient_supported hK g k Φ kp hp i) |>.sub
      ((NonzeroSupported.constant _).mul (vectorLaplacian_supported hK g k Φ kp ha i))).add
        (transport_supported hK g k Φ kp ha ha i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficients_sub (c d : HarmonicFields.Coefficients D) :
    realCoefficients (c - d) = realCoefficients c - realCoefficients d := by
  ext j x
  change realCoefficients (c - d) j x = realCoefficients c j x - realCoefficients d j x
  simp only [realCoefficients_apply]
  change (2 : ℂ)⁻¹ * (c j x - d j x + conj (c (-j) x - d (-j) x)) =
    (2 : ℂ)⁻¹ * (c j x + conj (c (-j) x)) -
    (2 : ℂ)⁻¹ * (d j x + conj (d (-j) x))
  rw [map_sub]
  ring


/-- The exact excluded nonzero coefficient.  Its mean part is removed
even when that part is not localized in a native slot. -/
noncomputable def excludedSource (G A : HarmonicResidual.BlockCoefficients D)
    (j : ℤ) (n : ℕ) (x : D) : ComplexVector := fun i =>
  -(nonconstant (realCoefficients (G n i))) j x -
    (nonconstant (realCoefficients (A n i))) j x

theorem residualSource_apply_ne_zero (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {j : ℤ} (hj : j ≠ 0) (n : ℕ) (x : D) (i : Fin 3) :
    ParticularWaveAssembly.residualSource c u b G A j n x i =
      realCoefficients (HarmonicResidual.nonlinearResidual (contextFrame c n)
        (b.frequency n) (b.phase n) (b.angularFrequency n)
        (constantVector (contextBase c n + stateMean u n))
        (ofBlock b G A n).velocity (ofBlock b G A n).pressure i) j x -
      realCoefficients (G n i) j x - realCoefficients (A n i) j x := by
  change nonconstant (realCoefficients (_ - _ - _)) j x = _
  simp only [HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase, Finsupp.erase_ne hj, realCoefficients_sub,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Pi.sub_apply]
  rfl





/-! ## Support of the actual real fields suffices -/

theorem nonlinear_ofBlock_supported_of_real {K : Set D} (hK : IsClosed K)
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (realCoefficients (b.velocity n i)))
    (hp : NonzeroSupported K (realCoefficients (b.pressure n))) :
    ∀ i, NonzeroSupported K
      (HarmonicResidual.nonlinearResidual (contextFrame c n) (b.frequency n) (b.phase n)
        (b.angularFrequency n) (constantVector (contextBase c n + stateMean u n))
        (ofBlock b G A n).velocity (ofBlock b G A n).pressure i) :=
  nonlinearResidual_supported hK _ _ _ _ (fun _ => NonzeroSupported.constant _) hv hp

theorem residualSource_outside_of_real
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {K : Set D} (hK : IsClosed K) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (realCoefficients (b.velocity n i)))
    (hp : NonzeroSupported K (realCoefficients (b.pressure n)))
    (j : ℤ) {x : D} (hx : x ∉ K) :
    ParticularWaveAssembly.residualSource c u b G A j n x = excludedSource G A j n x := by
  by_cases hj : j = 0
  · subst j
    rw [ParticularWaveAssembly.residualSource_zero]
    ext i
    simp [excludedSource, HarmonicResidual.nonconstant]
  · ext i
    rw [residualSource_apply_ne_zero c u b G A hj]
    have hn := ((nonlinear_ofBlock_supported_of_real hK c u b G A n hv hp i).realProjection)
      j hj x hx
    simp only [hn, excludedSource, HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase, Finsupp.erase_ne hj, zero_sub]


theorem residualSource_support_of_real
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {K : Set D} (hK : IsClosed K) (n : ℕ)
    (hv : ∀ i, NonzeroSupported K (realCoefficients (b.velocity n i)))
    (hp : NonzeroSupported K (realCoefficients (b.pressure n)))
    (hG : ∀ i, NonzeroSupported K (realCoefficients (G n i)))
    (hA : ∀ i, NonzeroSupported K (realCoefficients (A n i))) (j : ℤ) :
    support (ParticularWaveAssembly.residualSource c u b G A j n) ⊆ K := by
  intro x hx
  by_contra hnot
  apply hx
  rw [residualSource_outside_of_real c u b G A hK n hv hp j hnot]
  ext i
  by_cases hj : j = 0
  · simp [excludedSource, HarmonicResidual.nonconstant, hj]
  · simp only [excludedSource, HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase, Finsupp.erase_ne hj,
      hG i j hj x hnot, hA i j hj x hnot, neg_zero, sub_zero, Pi.zero_apply]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficient_eq_zero_of_field
    (c : HarmonicFields.Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (j : ℤ) (x : D)
    (hf : ∀ θ, (HarmonicFields.field c k Φ kp (x, θ)).re = 0) :
    realCoefficients c j x = 0 := by
  rw [← extract_field (realCoefficients c) k Φ hkp j x]
  simp only [extract, field_realCoefficients, hf, Complex.ofReal_zero, zero_mul]
  simp [HarmonicFields.angularMean]




/-! ## The uncovered source is estimated from its explicit excluded errors -/


/-! ## Coverage by all actual native copies -/

section NativeCoverage

open CommonCoverSolve TorusInverse TorusAverages

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def nativeUnion (g : Geometry) (K : Set Plane) : Set (P × Plane) :=
  ⋃ k : Frequency, PeriodizedWaveBounds.nativeCell g K k

omit [NormedSpace ℝ P] in
theorem nativeUnion_closed (g : Geometry) {K : Set Plane} (hK : IsCompact K) :
    IsClosed (nativeUnion (P := P) g K) :=
  (PeriodizedWaveBounds.nativeCell_locallyFinite g hK).isClosed_iUnion
    (PeriodizedWaveBounds.nativeCell_closed g hK.isClosed)



end NativeCoverage

/-! ## Different labels: genuine derivative products vanish on separated slots -/



section ColoredSlots

open CorrectionState LabelSumBounds

variable {ι : Type*} {d h : ℝ} {vr vt : TorusInverse.Plane}
  {sys : PartitionedCovariance.SlotSystem d h vr vt}
  {label : ℕ → ι → SlotColoring.Label} {χ : ℕ → D → WindowPoint}
  {Y : ℕ → D → TorusInverse.Plane} {U : Set D} {u v : ι → Oscillation D}




end ColoredSlots

/-! ## Relative support on the actual open strip -/

/-- Nonzero coefficients are supported in `K` relative to `U`.  Values
outside `U` are not constrained. -/
def NonzeroSupportedOn (U K : Set D) (c : HarmonicFields.Coefficients D) : Prop :=
  ∀ j : ℤ, j ≠ 0 → ∀ x : D, x ∈ U → x ∉ K → c j x = 0

namespace NonzeroSupportedOn

variable {U K : Set D} {c : HarmonicFields.Coefficients D}

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem enlarge (hc : NonzeroSupportedOn U K c) : NonzeroSupported (Uᶜ ∪ K) c := by
  intro j hj x hx
  apply hc j hj x
  · by_contra hn
    exact hx (Or.inl hn)
  · exact fun hk => hx (Or.inr hk)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem of_global (hc : NonzeroSupported K c) : NonzeroSupportedOn U K c :=
  fun j hj x _ hx => hc j hj x hx

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem of_enlarge (hc : NonzeroSupported (Uᶜ ∪ K) c) : NonzeroSupportedOn U K c :=
  fun j hj x hx hn => hc j hj x (by simpa using And.intro hx hn)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem add (hc : NonzeroSupportedOn U K c) {d : HarmonicFields.Coefficients D}
    (hd : NonzeroSupportedOn U K d) : NonzeroSupportedOn U K (c + d) :=
  of_enlarge (hc.enlarge.add hd.enlarge)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem sub (hc : NonzeroSupportedOn U K c) {d : HarmonicFields.Coefficients D}
    (hd : NonzeroSupportedOn U K d) : NonzeroSupportedOn U K (c - d) :=
  of_enlarge (hc.enlarge.sub hd.enlarge)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem mul (hc : NonzeroSupportedOn U K c) {d : HarmonicFields.Coefficients D}
    (hd : NonzeroSupportedOn U K d) : NonzeroSupportedOn U K (c * d) :=
  of_enlarge (hc.enlarge.mul hd.enlarge)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem constant (f : D → ℂ) : NonzeroSupportedOn U K (constantCoefficient f) :=
  of_global (NonzeroSupported.constant f)

theorem differentiate (hc : NonzeroSupportedOn U K c) (hU : IsOpen U) (hK : IsClosed K)
    (V : D → D) (k : ℝ) (Φ : D → ℝ) :
    NonzeroSupportedOn U K (HarmonicFields.differentiate V k Φ c) :=
  of_enlarge (hc.enlarge.differentiate (hU.isClosed_compl.union hK) V k Φ)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realProjection (hc : NonzeroSupportedOn U K c) :
    NonzeroSupportedOn U K (realCoefficients c) := by
  intro j hj x hx hn
  simp only [realCoefficients_apply, hc j hj x hx hn, hc (-j) (neg_ne_zero.mpr hj) x hx hn,
    map_zero, add_zero, mul_zero]

end NonzeroSupportedOn

/-- Primitive support data for the incoming block and its two excluded
error families.  There is no assumption about its residual or derivatives. -/
structure InputSupportOn (U : Set D) (K : ℕ → Set D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D) : Prop where
  velocity : ∀ n i, NonzeroSupportedOn U (K n) (realCoefficients (b.velocity n i))
  pressure : ∀ n, NonzeroSupportedOn U (K n) (realCoefficients (b.pressure n))
  gaussian : ∀ n i, NonzeroSupportedOn U (K n) (realCoefficients (G n i))
  aliasError : ∀ n i, NonzeroSupportedOn U (K n) (realCoefficients (A n i))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficients_supportedOn_of_field
    (c : HarmonicFields.Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) {U K : Set D}
    (hf : ∀ x, x ∈ U → x ∉ K → ∀ θ, (HarmonicFields.field c k Φ kp (x, θ)).re = 0) :
    NonzeroSupportedOn U K (realCoefficients c) :=
  fun j _ x hx hn => realCoefficient_eq_zero_of_field c k Φ hkp j x (hf x hx hn)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem InputSupportOn.of_fields
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {U : Set D} {K : ℕ → Set D} (hkp : ∀ n, b.angularFrequency n ≠ 0)
    (hv : ∀ n x, x ∈ U → x ∉ K n → ∀ θ i, b.oscillation n (x, θ) i = 0)
    (hp : ∀ n x, x ∈ U → x ∉ K n → ∀ θ, b.oscillatoryPressure n (x, θ) = 0)
    (hG : ∀ n x, x ∈ U → x ∉ K n → ∀ θ i,
      (HarmonicResidual.vectorField (G n) (b.frequency n) (b.phase n)
        (b.angularFrequency n) (x, θ) i).re = 0)
    (hA : ∀ n x, x ∈ U → x ∉ K n → ∀ θ i,
      (HarmonicResidual.vectorField (A n) (b.frequency n) (b.phase n)
        (b.angularFrequency n) (x, θ) i).re = 0) :
    InputSupportOn U K b G A := by
  constructor
  · intro n i
    exact realCoefficients_supportedOn_of_field _ _ _ (hkp n)
      (fun x hx hn θ => hv n x hx hn θ i)
  · intro n
    exact realCoefficients_supportedOn_of_field _ _ _ (hkp n) (hp n)
  · intro n i
    exact realCoefficients_supportedOn_of_field _ _ _ (hkp n)
      (fun x hx hn θ => hG n x hx hn θ i)
  · intro n i
    exact realCoefficients_supportedOn_of_field _ _ _ (hkp n)
      (fun x hx hn θ => hA n x hx hn θ i)


/-- The source has a genuine zero neighborhood at every uncovered point
of the open strip.  Only incoming coefficient support on that strip is used. -/
theorem residualSource_zero_germ_on
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {U : Set D} {K : ℕ → Set D} (hU : IsOpen U) (hK : ∀ n, IsClosed (K n))
    (hs : InputSupportOn U K b G A) (j : ℤ) (n : ℕ) {x : D}
    (hx : x ∈ U) (hn : x ∉ K n) :
    ParticularWaveAssembly.residualSource c u b G A j n =ᶠ[𝓝 x] fun _ => 0 := by
  apply PeriodizedWaveBounds.zero_germ_of_support (hU.isClosed_compl.union (hK n))
  · exact residualSource_support_of_real c u b G A (hU.isClosed_compl.union (hK n)) n
      (fun i => (hs.velocity n i).enlarge) (hs.pressure n).enlarge
      (fun i => (hs.gaussian n i).enlarge) (fun i => (hs.aliasError n i).enlarge) j
  · simpa using And.intro hx hn




section RelativeNativeCoverage

open CommonCoverSolve TorusInverse

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]




theorem sourceFamily_zero_germ_on
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : CorrectionState.HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane))
    (g : ℕ → Geometry) (K : ℕ → Set Plane) (hK : ∀ n, IsCompact (K n))
    {U : Set (P × Plane)} (hU : IsOpen U)
    (hs : InputSupportOn U (fun n => nativeUnion (g n) (K n)) b G A)
    (j : ℤ) (n : ℕ) {x : (P × ℝ) × Plane}
    (hx : (x.1.1, x.2) ∈ U)
    (hn : ∀ k, x ∉ PeriodizedWaveBounds.nativeCell (g n) (K n) k) :
    ParticularWaveAssembly.sourceFamily c u b G A j n =ᶠ[𝓝 x] fun _ => 0 := by
  have hnot : (x.1.1, x.2) ∉ nativeUnion (g n) (K n) := by
    simp only [nativeUnion, mem_iUnion, not_exists]
    exact hn
  have he := residualSource_zero_germ_on c u b G A hU
    (fun n => nativeUnion_closed (g n) (hK n)) hs j n hx hnot
  have hc : Continuous (fun y : (P × ℝ) × Plane => (y.1.1, y.2)) :=
    continuous_fst.fst.prodMk continuous_snd
  exact he.comp_tendsto hc.continuousAt


end RelativeNativeCoverage

/-! ## Unrestricted zero modes and the exact excluded-tail obstruction -/




end NavierStokes.HarmonicSourceSupport
