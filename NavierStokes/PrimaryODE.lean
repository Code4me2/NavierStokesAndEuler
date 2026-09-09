import NavierStokes.MovingFrameODE
import NavierStokes.SmoothPathFamily
import NavierStokes.WeightedODEJets
import NavierStokes.PulseCovariance
import NavierStokes.PhaseEstimates
import NavierStokes.JointODE

/-!
# Constructed primary pulse solutions

The operator and forcing are defined from the actual moving tangent frame.
The solution is the finite-interval Volterra solution, with its differentiable
extension.  Reconstruction into ambient coordinates satisfies the projected
equation exactly.  Estimates are derived for this constructed solution.
-/

noncomputable section

namespace NavierStokes.PrimaryODE

open Set Filter
open scoped Topology ContDiff InnerProductSpace

abbrev State := MovingFrameODE.Plane
abbrev Space := MovingFrameODE.Space
abbrev Frame := MovingFrameODE.Frame

/-- Smooth input quantities before any solution is constructed.  `eigenvector`
is the scalar `h` in `x=p+q, y=h(p-q)`; its logarithmic derivative is
`eigenRate`.  `viscosity` is the fundamental scalar damping. -/
structure FrameData (Q : Type) where
  beta : Q × ℝ → ℝ
  betaDot : Q × ℝ → ℝ
  rho : Q × ℝ → ℝ
  rhoDot : Q × ℝ → ℝ
  rotation : Q × ℝ → ℝ
  F : Q × ℝ → ℝ
  shear : Q × ℝ → State
  frame : Q × ℝ → Frame
  eigenvalue : Q × ℝ → ℝ
  eigenvector : Q × ℝ → ℝ
  eigenRate : Q × ℝ → ℝ
  viscosity : Q × ℝ → ℝ

namespace FrameData

variable {Q : Type} (d : FrameData Q)

noncomputable def errorA (z : Q × ℝ) : ℝ :=
  MovingFrameODE.coeff11 (d.rho z) (d.rhoDot z) ⟪d.frame z 0, d.shear z⟫_ℝ

noncomputable def errorB (z : Q × ℝ) : ℝ :=
  MovingFrameODE.coeff12 (d.F z) (d.frame z 1 0) (d.rho z) (d.rotation z) -
    d.eigenvalue z / d.eigenvector z

noncomputable def errorC (z : Q × ℝ) : ℝ :=
  MovingFrameODE.coeff21 (d.F z) (d.frame z 1 0) ⟪d.frame z 1, d.shear z⟫_ℝ
    (d.rho z) (d.rotation z) - d.eigenvalue z * d.eigenvector z

noncomputable def error11 (z : Q × ℝ) : ℝ :=
  MovingFrameODE.modal11 (d.errorA z) (d.errorB z) (d.errorC z)
    (d.eigenvector z) (d.eigenRate z)

noncomputable def error12 (z : Q × ℝ) : ℝ :=
  MovingFrameODE.modal12 (d.errorA z) (d.errorB z) (d.errorC z)
    (d.eigenvector z) (d.eigenRate z)

noncomputable def error21 (z : Q × ℝ) : ℝ :=
  MovingFrameODE.modal21 (d.errorA z) (d.errorB z) (d.errorC z)
    (d.eigenvector z) (d.eigenRate z)

noncomputable def error22 (z : Q × ℝ) : ℝ :=
  MovingFrameODE.modal22 (d.errorA z) (d.errorB z) (d.errorC z)
    (d.eigenvector z) (d.eigenRate z)

noncomputable def damping (j : ℤ) (z : Q × ℝ) : ℝ := (j : ℝ) ^ 2 * d.viscosity z

noncomputable def coefficient (j : ℤ) (z : Q × ℝ) : State →L[ℝ] State :=
  GrowingMode.modalOperator (d.eigenvalue z) (d.damping j z)
    (d.error11 z) (d.error12 z) (d.error21 z) (d.error22 z)

noncomputable def forceX (f : Q × ℝ → Space) (z : Q × ℝ) : ℝ :=
  -(f z 0 - d.rho z * ⟪d.frame z 0, MovingFrameODE.tail (f z)⟫_ℝ) /
    (1 + d.rho z ^ 2)

noncomputable def forceY (f : Q × ℝ → Space) (z : Q × ℝ) : ℝ :=
  -⟪d.frame z 1, MovingFrameODE.tail (f z)⟫_ℝ

noncomputable def forcing (f : Q × ℝ → Space) (z : Q × ℝ) : State :=
  !₂[(d.forceX f z + d.forceY f z / d.eigenvector z) / 2,
    (d.forceX f z - d.forceY f z / d.eigenvector z) / 2]

noncomputable def ambient (z : Q × ℝ) (w : State) : Space :=
  MovingFrameODE.tangent (d.rho z) (d.frame z) (w 0 + w 1)
    (d.eigenvector z * (w 0 - w 1))

noncomputable def normal (z : Q × ℝ) : Space :=
  MovingFrameODE.normal (d.beta z) (d.rho z) (d.frame z)

noncomputable def normalMotion (z : Q × ℝ) : Space :=
  MovingFrameODE.normalMotion (d.beta z) (d.betaDot z) (d.rho z) (d.rhoDot z)
    (d.rotation z) (d.frame z)

@[simp] theorem forcing_zero (z : Q × ℝ) : d.forcing (fun _ => 0) z = 0 := by
  ext i
  have hz : MovingFrameODE.tail (0 : Space) = 0 := by ext i; fin_cases i <;> rfl
  fin_cases i <;> simp [forcing, forceX, forceY, hz]

@[simp] theorem forcing_zero_function : d.forcing (fun _ => 0) = (fun _ => 0) :=
  funext d.forcing_zero

@[simp] theorem damping_one (z : Q × ℝ) : d.damping 1 z = d.viscosity z := by
  simp [damping]

theorem ambient_tangent (z : Q × ℝ) (w : State) :
    ⟪d.normal z, d.ambient z w⟫_ℝ = 0 :=
  MovingFrameODE.normal_tangent _ _ _ _ _

/-- Actual derivatives of the supplied frame data, without assumptions about
any ODE solution. -/
structure Kinematics (p : Q) (I : Set ℝ) : Prop where
  beta_ne_zero : ∀ v ∈ I, d.beta (p, v) ≠ 0
  eigenvector_ne_zero : ∀ v ∈ I, d.eigenvector (p, v) ≠ 0
  beta_deriv : ∀ v ∈ I,
    HasDerivAt (fun t => d.beta (p, t)) (d.betaDot (p, v)) v
  rho_deriv : ∀ v ∈ I,
    HasDerivAt (fun t => d.rho (p, t)) (d.rhoDot (p, v)) v
  eigenvector_deriv : ∀ v ∈ I,
    HasDerivAt (fun t => d.eigenvector (p, t))
      (d.eigenRate (p, v) * d.eigenvector (p, v)) v
  frameK_deriv : ∀ v ∈ I,
    HasDerivAt (fun t => d.frame (p, t) 0)
      (d.rotation (p, v) • d.frame (p, v) 1) v
  frameN_deriv : ∀ v ∈ I,
    HasDerivAt (fun t => d.frame (p, t) 1)
      (-d.rotation (p, v) • d.frame (p, v) 0) v

end FrameData

section Construction

variable {Q : Type} [NormedAddCommGroup Q]
variable {a b : ℝ}

/-- The differentiable extension of the actual Volterra solution. -/
noncomputable def extendedFamily (hab : a ≤ b)
    (A : Q × ℝ → State →L[ℝ] State) (x₀ : Q → State) (f : Q × ℝ → State)
    (p : Q) : ℝ → State :=
  ParametricODE.solutionExtension hab (SmoothPathFamily.pathFamily A p) (x₀ p)
    (SmoothPathFamily.pathFamily f p)

omit [NormedAddCommGroup Q] in
theorem extendedFamily_eq_path (hab : a ≤ b)
    (A : Q × ℝ → State →L[ℝ] State) (x₀ : Q → State) (f : Q × ℝ → State)
    (p : Q) (v : Icc a b) :
    extendedFamily hab A x₀ f p v = SmoothPathFamily.odeFamily hab A x₀ f p v :=
  ParametricODE.solutionExtension_coe _ _ _ _ _

omit [NormedAddCommGroup Q] in
theorem extendedFamily_initial (hab : a ≤ b)
    (A : Q × ℝ → State →L[ℝ] State) (x₀ : Q → State) (f : Q × ℝ → State)
    (p : Q) : extendedFamily hab A x₀ f p a = x₀ p := by
  exact (extendedFamily_eq_path hab A x₀ f p ⟨a, le_rfl, hab⟩).trans
    (SmoothPathFamily.odeFamily_initial _ _ _ _ _)

theorem extendedFamily_hasDerivAt (hab : a ≤ b) {U : Set Q}
    (A : Q × ℝ → State →L[ℝ] State) (x₀ : Q → State) (f : Q × ℝ → State)
    (hA : ContinuousOn A (U ×ˢ Icc a b)) (hf : ContinuousOn f (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) {v : ℝ} (hv : v ∈ Icc a b) :
    HasDerivAt (extendedFamily hab A x₀ f p)
      (A (p, v) (extendedFamily hab A x₀ f p v) + f (p, v)) v := by
  have hAc := SmoothPathFamily.slice_continuous hA hp
  have hfc := SmoothPathFamily.slice_continuous hf hp
  have hh := ParametricODE.solutionExtension_hasDerivAt hab
    (SmoothPathFamily.pathFamily A p) (x₀ p) (SmoothPathFamily.pathFamily f p) ⟨v, hv⟩
  unfold extendedFamily
  simpa only [SmoothPathFamily.pathFamily_apply A p hAc,
    SmoothPathFamily.pathFamily_apply f p hfc] using hh

noncomputable def solution (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) (p : Q) : ℝ → State :=
  extendedFamily hab (d.coefficient j) x₀ (d.forcing f) p

noncomputable def ambientSolution (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) (p : Q) (v : ℝ) : Space :=
  d.ambient (p, v) (solution hab d j x₀ f p v)

omit [NormedAddCommGroup Q] in
theorem solution_initial (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) (p : Q) :
    solution hab d j x₀ f p a = x₀ p :=
  extendedFamily_initial _ _ _ _ _

theorem solution_hasDerivAt (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) {U : Set Q}
    (hA : ContinuousOn (d.coefficient j) (U ×ˢ Icc a b))
    (hf : ContinuousOn (d.forcing f) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) {v : ℝ} (hv : v ∈ Icc a b) :
    HasDerivAt (solution hab d j x₀ f p)
      (d.coefficient j (p, v) (solution hab d j x₀ f p v) + d.forcing f (p, v)) v :=
  extendedFamily_hasDerivAt _ _ _ _ hA hf hp hv

omit [NormedAddCommGroup Q] in
theorem ambientSolution_tangent (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) (p : Q) (v : ℝ) :
    ⟪d.normal (p, v), ambientSolution hab d j x₀ f p v⟫_ℝ = 0 :=
  d.ambient_tangent _ _

/-- Exact reconstruction into equation (27), including the projected physical
forcing and harmonic-dependent scalar viscosity. -/
theorem ambientSolution_hasDerivAt (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) {U : Set Q}
    (hA : ContinuousOn (d.coefficient j) (U ×ˢ Icc a b))
    (hf : ContinuousOn (d.forcing f) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) (hk : d.Kinematics p (Icc a b)) {v : ℝ} (hv : v ∈ Icc a b) :
    HasDerivAt (ambientSolution hab d j x₀ f p)
      (TangentProjection.projectedRhs (d.normal (p, v)) (d.normalMotion (p, v))
        (ambientSolution hab d j x₀ f p v)
        (MovingFrameODE.baseAction (d.F (p, v)) (d.shear (p, v))
          (ambientSolution hab d j x₀ f p v))
        (f (p, v)) (d.damping j (p, v))) v := by
  let z := solution hab d j x₀ f p
  let z' := d.coefficient j (p, v) (z v) + d.forcing f (p, v)
  have hz : HasDerivAt z z' v := solution_hasDerivAt hab d j x₀ f hA hf hp hv
  have hplus := GrowingMode.hasDerivAt_coordinate hz 0
  have hminus := GrowingMode.hasDerivAt_coordinate hz 1
  have hx := hplus.fun_add hminus
  have hy := (hk.eigenvector_deriv v hv).fun_mul (hplus.fun_sub hminus)
  apply (MovingFrameODE.hasDerivAt_projected_iff (β' := d.betaDot (p, v))
    (hk.beta_ne_zero v hv) (hk.rho_deriv v hv) hx hy
    (hk.frameK_deriv v hv) (hk.frameN_deriv v hv)).mpr
  have hm := (MovingFrameODE.modal_equations_iff (hk.eigenvector_ne_zero v hv)
    (z v 0) (z v 1) (z' 0) (z' 1) (d.eigenvalue (p, v)) (d.damping j (p, v))
    (d.errorA (p, v)) (d.errorB (p, v)) (d.errorC (p, v)) (d.eigenRate (p, v))
    (d.forceX f (p, v)) (d.forceY f (p, v))).mpr
      ⟨by rfl, by rfl⟩
  constructor
  · convert! hm.1 using 1
    simp only [FrameData.errorA, FrameData.errorB, FrameData.forceX, MovingFrameODE.rhsX]
    ring
  · convert! hm.2 using 1
    simp only [FrameData.errorC, FrameData.forceY, MovingFrameODE.rhsY]
    ring

end Construction

section Smooth

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Smoothness of the explicit input fields.  Frame smoothness means smoothness
of each ambient basis vector, avoiding an arbitrary manifold structure on
the space of orthonormal bases. -/
structure FrameData.SmoothOn (d : FrameData Q) (Ω : Set (Q × ℝ)) : Prop where
  beta : ContDiffOn ℝ ∞ d.beta Ω
  betaDot : ContDiffOn ℝ ∞ d.betaDot Ω
  rho : ContDiffOn ℝ ∞ d.rho Ω
  rhoDot : ContDiffOn ℝ ∞ d.rhoDot Ω
  rotation : ContDiffOn ℝ ∞ d.rotation Ω
  F : ContDiffOn ℝ ∞ d.F Ω
  shear : ContDiffOn ℝ ∞ d.shear Ω
  frame : ∀ i, ContDiffOn ℝ ∞ (fun z => d.frame z i) Ω
  eigenvalue : ContDiffOn ℝ ∞ d.eigenvalue Ω
  eigenvector : ContDiffOn ℝ ∞ d.eigenvector Ω
  eigenRate : ContDiffOn ℝ ∞ d.eigenRate Ω
  viscosity : ContDiffOn ℝ ∞ d.viscosity Ω
  eigenvector_ne_zero : ∀ z ∈ Ω, d.eigenvector z ≠ 0

theorem FrameData.SmoothOn.errorA {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) : ContDiffOn ℝ ∞ d.errorA Ω := by
  exact (h.rho.mul (((h.frame 0).inner ℝ h.shear).sub h.rhoDot)).div
    (contDiffOn_const.add (h.rho.pow 2)) (fun z _ => by positivity)

theorem FrameData.SmoothOn.errorB {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) : ContDiffOn ℝ ∞ d.errorB Ω := by
  have hn : ContDiffOn ℝ ∞ (fun z => d.frame z 1 0) Ω :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)).comp_contDiffOn (h.frame 1)
  exact (((contDiffOn_const.mul h.F).mul hn).sub (h.rho.mul h.rotation)).div
    (contDiffOn_const.add (h.rho.pow 2)) (fun z _ => by positivity) |>.sub
      (h.eigenvalue.div h.eigenvector h.eigenvector_ne_zero)

theorem FrameData.SmoothOn.errorC {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) : ContDiffOn ℝ ∞ d.errorC Ω := by
  have hn : ContDiffOn ℝ ∞ (fun z => d.frame z 1 0) Ω :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)).comp_contDiffOn (h.frame 1)
  exact ((((contDiffOn_const.mul h.F).mul hn).add ((h.frame 1).inner ℝ h.shear)).neg.add
    (h.rho.mul h.rotation)).sub (h.eigenvalue.mul h.eigenvector)

theorem FrameData.SmoothOn.modal_errors {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) :
    ContDiffOn ℝ ∞ d.error11 Ω ∧ ContDiffOn ℝ ∞ d.error12 Ω ∧
      ContDiffOn ℝ ∞ d.error21 Ω ∧ ContDiffOn ℝ ∞ d.error22 Ω := by
  have hb := h.eigenvector.mul h.errorB
  have hc := h.errorC.div h.eigenvector h.eigenvector_ne_zero
  exact ⟨(((h.errorA.add hb).add hc).sub h.eigenRate).div_const 2,
    (((h.errorA.sub hb).add hc).add h.eigenRate).div_const 2,
    (((h.errorA.add hb).sub hc).add h.eigenRate).div_const 2,
    (((h.errorA.sub hb).sub hc).sub h.eigenRate).div_const 2⟩

private theorem modalOperator_expansion (lam damping e11 e12 e21 e22 : ℝ) :
    GrowingMode.modalOperator lam damping e11 e12 e21 e22 =
      (lam - damping + e11) • GrowingMode.modalOperator 0 0 1 0 0 0 +
      e12 • GrowingMode.modalOperator 0 0 0 1 0 0 +
      e21 • GrowingMode.modalOperator 0 0 0 0 1 0 +
      (-lam - damping + e22) • GrowingMode.modalOperator 0 0 0 0 0 1 := by
  ext z i
  fin_cases i <;> simp [GrowingMode.modalOperator]

theorem FrameData.SmoothOn.coefficient {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) (j : ℤ) : ContDiffOn ℝ ∞ (d.coefficient j) Ω := by
  rcases h.modal_errors with ⟨h11, h12, h21, h22⟩
  have hd : ContDiffOn ℝ ∞ (d.damping j) Ω := contDiffOn_const.mul h.viscosity
  have hh := ((((h.eigenvalue.sub hd).add h11).smul
    (contDiffOn_const (c := GrowingMode.modalOperator 0 0 1 0 0 0))).add
    (h12.smul (contDiffOn_const (c := GrowingMode.modalOperator 0 0 0 1 0 0))) |>.add
      (h21.smul (contDiffOn_const (c := GrowingMode.modalOperator 0 0 0 0 1 0)))).add
        (((h.eigenvalue.neg.sub hd).add h22).smul
          (contDiffOn_const (c := GrowingMode.modalOperator 0 0 0 0 0 1)))
  apply hh.congr
  intro z _
  exact modalOperator_expansion _ _ _ _ _ _

theorem FrameData.SmoothOn.forcing {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) {f : Q × ℝ → Space} (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (d.forcing f) Ω := by
  have ht := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    MovingFrameODE.tailCLM).comp_contDiffOn hf
  have hr := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0)).comp_contDiffOn hf
  have hx : ContDiffOn ℝ ∞ (d.forceX f) Ω :=
    (hr.sub (h.rho.mul ((h.frame 0).inner ℝ ht))).neg.div
      (contDiffOn_const.add (h.rho.pow 2)) (fun z _ => by positivity)
  have hy : ContDiffOn ℝ ∞ (d.forceY f) Ω := ((h.frame 1).inner ℝ ht).neg
  have hdiv := hy.div h.eigenvector h.eigenvector_ne_zero
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) MovingFrameODE.pairCLM).comp_contDiffOn
    (((hx.add hdiv).div_const 2).prodMk ((hx.sub hdiv).div_const 2))


end Smooth


/-- Scalar viscosity keeps the same sign at every nonzero integer harmonic.
The modal energy estimate is derived from entrywise coefficient errors. -/
theorem FrameData.energy_bound {Q : Type} (d : FrameData Q) (z : Q × ℝ)
    {j : ℤ} (hj : j ≠ 0) {referenceDamping C D S : ℝ}
    (hlam : 0 ≤ d.eigenvalue z) (hν : 0 ≤ d.viscosity z)
    (hνerr : referenceDamping - D / S ≤ d.viscosity z)
    (herr : |d.error11 z| ≤ C / S ∧ |d.error12 z| ≤ C / S ∧
      |d.error21 z| ≤ C / S ∧ |d.error22 z| ≤ C / S) (w : State) :
    ⟪w, d.coefficient j z w⟫_ℝ ≤
      (d.eigenvalue z - referenceDamping + (D + 4 * C) / S) * ‖w‖ ^ 2 := by
  have hd := ViscousPropagator.high_harmonic_damping hj hν hνerr
  have he := MovingFrameODE.modal_energy_le hlam (d.damping j z)
    herr.1 herr.2.1 herr.2.2.1 herr.2.2.2 w
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  change _ - (j : ℝ) ^ 2 * d.viscosity z + _ ≤ _
  rw [show (D + 4 * C) / S = D / S + 4 * (C / S) by ring]
  linarith

section Primary

variable {Q : Type} [NormedAddCommGroup Q]
variable {a b : ℝ}

noncomputable def primarySeed (a : ℝ) (P : Q × ℝ → ℝ) (p : Q) : State := !₂[P (p, a), 0]

noncomputable def primary (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ) (p : Q) : ℝ → State :=
  solution hab d 1 (primarySeed a P) (fun _ => 0) p

noncomputable def radialPrimary (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ)
    (p : Q) (v : ℝ) : ℝ := primary hab d P p v 0 + primary hab d P p v 1

noncomputable def transversePrimary (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ)
    (p : Q) (v : ℝ) : ℝ :=
  d.eigenvector (p, v) * (primary hab d P p v 0 - primary hab d P p v 1)

omit [NormedAddCommGroup Q] in
theorem primary_initial (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ) (p : Q) :
    primary hab d P p a = !₂[P (p, a), 0] := solution_initial _ _ _ _ _ _

theorem primary_hasDerivAt (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ)
    {U : Set Q} (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) {v : ℝ} (hv : v ∈ Icc a b) :
    HasDerivAt (primary hab d P p)
      (d.coefficient 1 (p, v) (primary hab d P p v)) v := by
  have hf : ContinuousOn (d.forcing (fun _ => 0)) (U ×ˢ Icc a b) := by
    simpa only [FrameData.forcing_zero_function] using
      (continuousOn_const : ContinuousOn (fun _ : Q × ℝ => (0 : State)) (U ×ˢ Icc a b))
  unfold primary
  simpa only [FrameData.forcing_zero, add_zero] using
    solution_hasDerivAt hab d 1 (primarySeed a P) (fun _ => 0) hA hf hp hv

/-- The actual constructed real primary has positive radial component,
two-sided reference-envelope comparison, and a small eigenvector ratio error.
Only coefficient estimates and the scalar reference equation are inputs. -/
theorem primary_bounds (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ)
    {U : Set Q} (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) {S C D L lammin : ℝ}
    (hlammin : 0 < lammin) (hC : 0 ≤ C) (hD : 0 ≤ D) (hS : 0 < S)
    (hlarge : 2 * GrowingMode.coneConstant lammin C ≤ S) (hslot : b - a ≤ L * S)
    (referenceDamping : ℝ → ℝ)
    (hlam : ∀ v ∈ Icc a b, lammin ≤ d.eigenvalue (p, v))
    (herr : ∀ v ∈ Icc a b,
      |d.error11 (p, v)| ≤ C / S ∧ |d.error12 (p, v)| ≤ C / S ∧
      |d.error21 (p, v)| ≤ C / S ∧ |d.error22 (p, v)| ≤ C / S)
    (hν : ∀ v ∈ Icc a b, |d.viscosity (p, v) - referenceDamping v| ≤ D / S)
    (hPpos : ∀ v ∈ Icc a b, 0 < P (p, v))
    (hP : ∀ v ∈ Icc a b, HasDerivAt (fun t => P (p, t))
      ((d.eigenvalue (p, v) - referenceDamping v) * P (p, v)) v) :
    ∀ v ∈ Icc a b,
      0 < radialPrimary hab d P p v ∧
      (Real.exp (-(D + 2 * C) * L) / 2) * P (p, v) ≤ radialPrimary hab d P p v ∧
      radialPrimary hab d P p v ≤ (3 * Real.exp ((D + 2 * C) * L) / 2) * P (p, v) ∧
      |transversePrimary hab d P p v / radialPrimary hab d P p v - d.eigenvector (p, v)| ≤
        4 * |d.eigenvector (p, v)| * (GrowingMode.coneConstant lammin C / S) := by
  have hAslice : ContinuousOn (fun v => d.coefficient 1 (p, v)) (Icc a b) :=
    hA.comp (continuous_const.prodMk continuous_id).continuousOn (fun v hv => ⟨hp, hv⟩)
  have hAi : ContinuousOn (fun v => GrowingMode.modalOperator (d.eigenvalue (p, v))
      (d.viscosity (p, v)) (d.error11 (p, v)) (d.error12 (p, v))
      (d.error21 (p, v)) (d.error22 (p, v))) (Icc a b) := by
    simpa only [FrameData.coefficient, FrameData.damping_one] using hAslice
  have hode (v : ℝ) (hv : v ∈ Icc a b) := primary_hasDerivAt hab d P hA hp hv
  simp only [FrameData.coefficient, FrameData.damping_one] at hode
  have hplus : 0 < primary hab d P p a 0 := by
    rw [primary_initial]
    exact hPpos a ⟨le_rfl, hab⟩
  have hminus : primary hab d P p a 1 = 0 := by rw [primary_initial]; rfl
  have hm := GrowingMode.scaled_growing_mode_bounds hab hlammin hC hD hS hlarge hslot
    (fun v => d.eigenvalue (p, v)) (fun v => d.viscosity (p, v)) referenceDamping
    (fun v => d.error11 (p, v)) (fun v => d.error12 (p, v))
    (fun v => d.error21 (p, v)) (fun v => d.error22 (p, v))
    (fun v => P (p, v)) hAi hode hlam herr hν hPpos hP hplus hminus
  have hratio : primary hab d P p a 0 / P (p, a) = 1 := by
    rw [primary_initial]
    exact div_self (hPpos a ⟨le_rfl, hab⟩).ne'
  simp only [hratio, mul_one] at hm
  obtain ⟨hr, hrhalf, _⟩ := GrowingMode.scaled_cone_conditions hlammin hC hS hlarge
  intro v hv
  obtain ⟨hzpos, hzcone, hzlo, hzhi⟩ := hm v hv
  obtain ⟨hxlo, hxhi, hxratio⟩ := GrowingMode.original_coordinate_bounds
    (h := d.eigenvector (p, v)) hzpos hr.le hrhalf hzcone
  refine ⟨?_, ?_, ?_, hxratio⟩
  · change 0 < primary hab d P p v 0 + primary hab d P p v 1
    linarith
  · change _ ≤ primary hab d P p v 0 + primary hab d P p v 1
    nlinarith
  · change primary hab d P p v 0 + primary hab d P p v 1 ≤ _
    nlinarith

end Primary

section Forward

variable {Q : Type} [NormedAddCommGroup Q]
variable {a b : ℝ}




end Forward

section PhaseFrame

variable {Q : Type}






end PhaseFrame

section ParameterJets

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]


end ParameterJets

noncomputable def referenceProfile (c₀ u ell v : ℝ) : ℝ :=
  c₀ * Real.sqrt (1 + PulseGrowth.slotMagnitude u ell v ^ 2)

noncomputable def referenceProfileRate (u ell v : ℝ) : ℝ :=
  PulseGrowth.slotMagnitude u ell v * (u / ell) /
    (1 + PulseGrowth.slotMagnitude u ell v ^ 2)

theorem hasDerivAt_referenceProfile (c₀ u ell v : ℝ) :
    HasDerivAt (referenceProfile c₀ u ell)
      (referenceProfileRate u ell v * referenceProfile c₀ u ell v) v := by
  have hs : HasDerivAt (PulseGrowth.slotMagnitude u ell) (u / ell) v := by
    unfold PulseGrowth.slotMagnitude
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id v).const_mul u).div_const ell).const_add (u / 2)
  have hr := ((hs.fun_pow 2).const_add 1).sqrt (by positivity)
  convert! hr.const_mul c₀ using 1
  unfold referenceProfileRate referenceProfile
  have hp := PulseGrowth.radius_pos (PulseGrowth.slotMagnitude u ell v)
  have hsq := Real.sq_sqrt (PulseGrowth.one_add_sq_pos (PulseGrowth.slotMagnitude u ell v)).le
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize u / ell = q
  field_simp [hp.ne', (PulseGrowth.one_add_sq_pos (PulseGrowth.slotMagnitude u ell v)).ne']
  nlinarith only [congrArg (fun z : ℝ => c₀ * PulseGrowth.slotMagnitude u ell v * q * z) hsq]

theorem referenceProfile_ne_zero {c₀ : ℝ} (hc₀ : c₀ ≠ 0) (u ell v : ℝ) :
    referenceProfile c₀ u ell v ≠ 0 :=
  mul_ne_zero hc₀ (PulseGrowth.radius_pos _).ne'

theorem referenceEigenvalue_lower {lam u ell v : ℝ} (hlam : 0 < lam) (hu : 0 ≤ u)
    (hell : 0 < ell) (hv : v ∈ Icc 0 ell) :
    lam / Real.sqrt (1 + (3 * u / 2) ^ 2) ≤ ViscousPropagator.referenceEigenvalue lam u ell v := by
  have hs := GaussianEnvelope.slotMagnitude_mem_interval hu hell hv
  have hs0 := PulseGrowth.slotMagnitude_nonneg hu hell hv.1
  apply div_le_div_of_nonneg_left hlam.le (PulseGrowth.radius_pos _)
  apply Real.sqrt_le_sqrt
  nlinarith [hs.2]


section GaussianPrimary

variable {Q : Type} [NormedAddCommGroup Q]


end GaussianPrimary

section SmoothPrimary

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]







end SmoothPrimary

section Joint

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]



end Joint






section AmbientForward

variable {Q : Type} [NormedAddCommGroup Q]


end AmbientForward

section LocalPhaseFrame

variable {Q : Type}

/-- Total frame selection.  The fallback is outside the nonvanishing phase
chart and imposes no hypothesis on those unused parameter values. -/
noncomputable def localFrame (n : Space) : Frame := by
  classical
  exact if hn : MovingFrameODE.tail n ≠ 0 then MovingFrameODE.normalFrame n hn
    else EuclideanSpace.basisFun (Fin 2) ℝ

theorem localFrame_eq {n : Space} (hn : MovingFrameODE.tail n ≠ 0) :
    localFrame n = MovingFrameODE.normalFrame n hn := by
  simp [localFrame, hn]

/-- The actual phase-derived coefficients require nonvanishing only on the
chart where they are used. -/
noncomputable def FrameData.ofNormalLocal (n nDot : Q × ℝ → Space)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) : FrameData Q where
  beta z := MovingFrameODE.normalScale (n z)
  betaDot z := PhaseEstimates.scaleDerivative (n z) (nDot z)
  rho z := MovingFrameODE.radialSlope (n z)
  rhoDot z := PhaseEstimates.slopeDerivative (n z) (nDot z)
  rotation z := PhaseEstimates.angularVelocity (n z) (nDot z)
  F := F
  shear := g
  frame z := localFrame (n z)
  eigenvalue := lam
  eigenvector := h
  eigenRate := hRate
  viscosity z := viscosityScale z * ‖n z‖ ^ 2

theorem FrameData.ofNormalLocal_normal (n nDot : Q × ℝ → Space)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) {z : Q × ℝ}
    (hn : MovingFrameODE.tail (n z) ≠ 0) :
    (FrameData.ofNormalLocal n nDot F g lam h hRate viscosityScale).normal z = n z := by
  change MovingFrameODE.normal _ _ (localFrame (n z)) = n z
  rw [localFrame_eq hn]
  exact MovingFrameODE.normal_reconstructed hn

theorem FrameData.ofNormalLocal_kinematics (n nDot : Q × ℝ → Space)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) (p : Q) (I : Set ℝ)
    (hn : ∀ v ∈ I, HasDerivAt (fun t => n (p, t)) (nDot (p, v)) v)
    (hne : ∀ v ∈ I, MovingFrameODE.tail (n (p, v)) ≠ 0)
    (hh : ∀ v ∈ I, h (p, v) ≠ 0)
    (hdh : ∀ v ∈ I, HasDerivAt (fun t => h (p, t)) (hRate (p, v) * h (p, v)) v) :
    (FrameData.ofNormalLocal n nDot F g lam h hRate viscosityScale).Kinematics p I := by
  have hframe (v : ℝ) (hv : v ∈ I) (i : Fin 2) :
      (fun t => localFrame (n (p, t)) i) =ᶠ[𝓝 v]
        (fun t => if i = 0 then MovingFrameODE.normalDirection (n (p, t))
          else MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (n (p, t)))) := by
    have ht := MovingFrameODE.tailCLM.hasFDerivAt.comp_hasDerivAt v (hn v hv)
    filter_upwards [ht.continuousAt.eventually_ne (hne v hv)] with t ht'
    rw [localFrame_eq ht']
    fin_cases i
    · simpa only [Fin.zero_eta, ↓reduceIte] using MovingFrameODE.normalFrame_zero (n (p, t)) ht'
    · simpa only [Fin.mk_one, one_ne_zero, ↓reduceIte] using MovingFrameODE.normalFrame_one (n (p, t)) ht'
  refine ⟨fun v hv => (MovingFrameODE.normalScale_pos (hne v hv)).ne', hh,
    ?_, ?_, hdh, ?_, ?_⟩
  · intro v hv
    exact PhaseEstimates.hasDerivAt_normalScale (hn v hv) (hne v hv)
  · intro v hv
    exact PhaseEstimates.hasDerivAt_radialSlope (hn v hv) (hne v hv)
  · intro v hv
    have he := hframe v hv 0
    simp only [ite_true] at he
    have hd := (PhaseEstimates.hasDerivAt_actual_frame (hn v hv) (hne v hv)).1
    have hk := hd.congr_of_eventuallyEq he
    simpa only [FrameData.ofNormalLocal, localFrame_eq (hne v hv), MovingFrameODE.normalFrame_one] using hk
  · intro v hv
    have he := hframe v hv 1
    simp only [one_ne_zero, ite_false] at he
    have hd := (PhaseEstimates.hasDerivAt_actual_frame (hn v hv) (hne v hv)).2
    have hk := hd.congr_of_eventuallyEq he
    simpa only [FrameData.ofNormalLocal, localFrame_eq (hne v hv), MovingFrameODE.normalFrame_zero] using hk

theorem FrameData.ofNormalLocal_normalMotion (n nDot : Q × ℝ → Space)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) {p : Q} {v : ℝ}
    (hn : HasDerivAt (fun t => n (p, t)) (nDot (p, v)) v)
    (hne : MovingFrameODE.tail (n (p, v)) ≠ 0) :
    (FrameData.ofNormalLocal n nDot F g lam h hRate viscosityScale).normalMotion (p, v) = nDot (p, v) := by
  have htail := MovingFrameODE.tailCLM.hasFDerivAt.comp_hasDerivAt v hn
  have hnear := htail.continuousAt.eventually_ne hne
  have hKeq : (fun t => localFrame (n (p, t)) 0) =ᶠ[𝓝 v]
      (fun t => MovingFrameODE.normalDirection (n (p, t))) := by
    filter_upwards [hnear] with t ht
    rw [localFrame_eq ht]
    exact MovingFrameODE.normalFrame_zero (n (p, t)) ht
  have hK : HasDerivAt (fun t => localFrame (n (p, t)) 0)
      (PhaseEstimates.angularVelocity (n (p, v)) (nDot (p, v)) • localFrame (n (p, v)) 1) v := by
    simpa only [localFrame_eq hne, MovingFrameODE.normalFrame_one] using
      (PhaseEstimates.hasDerivAt_actual_frame hn hne).1.congr_of_eventuallyEq hKeq
  have hd := MovingFrameODE.hasDerivAt_normal
    (PhaseEstimates.hasDerivAt_normalScale hn hne) (PhaseEstimates.hasDerivAt_radialSlope hn hne) hK
  have heq : (fun t => n (p, t)) =ᶠ[𝓝 v]
      (fun t => MovingFrameODE.normal (MovingFrameODE.normalScale (n (p, t)))
        (MovingFrameODE.radialSlope (n (p, t))) (localFrame (n (p, t)))) := by
    filter_upwards [hnear] with t ht
    rw [localFrame_eq ht]
    exact (MovingFrameODE.normal_reconstructed ht).symm
  exact (hd.congr_of_eventuallyEq heq).unique hn

end LocalPhaseFrame

end NavierStokes.PrimaryODE
