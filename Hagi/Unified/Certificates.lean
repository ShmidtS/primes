/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Foundations.Potential

/-!
# Certificates — typed per-stage certificates

Per-stage measured (h_emp_-contract) structures:
`GrowCertificate`, `MergeCertificate`, `JointCertificate`
(SafeQP alignment + quadratic slack), `CompressionCertificate`
(energy increases by at most `kappa * qerr`),
`GeneralizationCertificate` (probe drop `epsQ ≥ 0`), and the
chained bundle `CycleCertificate` (each stage's pre-state is
the previous stage's post-state).

`cycle_certificate_sound`: one certified cycle decreases the
potential Φ = E + λR + ν·max(0, Q_target − Q) whenever
`λ·(total risk) + ν·ε_Q ≤ dec` with
`dec = gap + η·⟪g,d⟫ − (L/2)η²‖d‖² − κ·qerr`.
-/

open scoped BigOperators

namespace Hagi.System

/-! ## Per-stage certificates -/

/-- The grow-stage certificate: nonneg capability gain,
energy drop BY the gain, physical (nonneg) risk. -/
structure GrowCertificate where
  preEnergy : ℝ
  energy : ℝ
  gain : ℝ
  risk : ℝ
  hgain : 0 ≤ gain
  hdrop : energy ≤ preEnergy - gain
  hrisk : 0 ≤ risk

/-- The merge-stage certificate: nonnegative Jensen gap,
energy drops BY the gap, physical risk. -/
structure MergeCertificate where
  preEnergy : ℝ
  energy : ℝ
  gap : ℝ
  risk : ℝ
  hgap : 0 ≤ gap
  hdrop : energy ≤ preEnergy - gap
  hrisk : 0 ≤ risk

/-- The safe joint-step certificate: the SafeQP descent
alignment and the quadratic-model slack. -/
structure JointCertificate where
  preEnergy : ℝ
  energy : ℝ
  inner : ℝ
  dnorm2 : ℝ
  eta : ℝ
  lip : ℝ
  risk : ℝ
  spend : ℝ
  halign : dnorm2 ≤ inner
  hquad : energy ≤ preEnergy - eta * inner
      + lip * eta * eta * dnorm2 / 2
  hetapt : 0 < eta
  hlip : 0 ≤ lip
  hrisk : 0 ≤ risk
  hspend : 0 ≤ spend

/-- The compression-stage certificate: quantization error
with the κ-slack (compression adds ≤ κ·qerr energy). -/
structure CompressionCertificate where
  preEnergy : ℝ
  energy : ℝ
  qerr : ℝ
  kappa : ℝ
  hkappa : 0 ≤ kappa
  hslack : energy ≤ preEnergy + kappa * qerr

/-- The generalization certificate: probe drop ε_Q ≥ 0. -/
structure GeneralizationCertificate where
  epsQ : ℝ
  q : ℝ
  q' : ℝ
  heps : 0 ≤ epsQ
  hdrop : q - epsQ ≤ q'

/-- The full cycle certificate: the bundle + the stage
chaining (each pre-state IS the previous post-state). -/
structure CycleCertificate where
  grow : GrowCertificate
  merge : MergeCertificate
  joint : JointCertificate
  compress : CompressionCertificate
  generalization : GeneralizationCertificate
  chain_gm : merge.preEnergy = grow.energy
  chain_mj : joint.preEnergy = merge.energy
  chain_jc : compress.preEnergy = joint.energy

/-! ## Soundness: one certified cycle decreases Φ -/

/-- The HAGI potential Φ = E + λR + ν·max(0, Q_target−Q). -/
noncomputable def hagiPotential (E R nu qTarget q : ℝ) (lam : ℝ) : ℝ :=
  -- R263 dedup: canonical form in Foundations.Potential
  Hagi.Foundations.hagiPotential E R nu qTarget q lam

/-- The penalty term grows by at most the probe drop. -/
lemma penalty_drop_bound (qTarget q q' epsQ : ℝ)
    (heps : 0 ≤ epsQ) (hdrop : q - epsQ ≤ q') :
    max 0 (qTarget - q') ≤ max 0 (qTarget - q) + epsQ := by
  have h1 : qTarget - q' ≤ qTarget - q + epsQ := by linarith
  have hkey : qTarget - q' ≤ max 0 (qTarget - q) + epsQ := by
    rcases le_total 0 (qTarget - q) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  rcases le_total 0 (qTarget - q') with h | h
  · rw [max_eq_right h]; exact hkey
  · rw [max_eq_left h]; positivity

/-- For a chained `CycleCertificate` with `lam, nu ≥ 0` and
price coverage `lam·(grow.risk + merge.risk + joint.risk) +
nu·epsQ ≤ dec` (dec as in the statement), the post-cycle
potential satisfies Φ' ≤ Φ for
`hagiPotential E R nu qTarget q lam`. -/
theorem cycle_certificate_sound
    (cert : CycleCertificate)
    (lam nu qTarget q R : ℝ)
    (hlam : 0 ≤ lam) (hnu : 0 ≤ nu)
    (hprice : lam * (cert.grow.risk + cert.merge.risk
        + cert.joint.risk) + nu * cert.generalization.epsQ
      ≤ cert.merge.gap + cert.joint.eta * cert.joint.inner
        - cert.joint.lip * cert.joint.eta
          * cert.joint.eta * cert.joint.dnorm2 / 2
        - cert.compress.kappa * cert.compress.qerr) :
    hagiPotential cert.compress.energy
        (R + cert.grow.risk + cert.merge.risk
          + cert.joint.risk) nu qTarget
        cert.generalization.q' lam
      ≤ hagiPotential cert.grow.preEnergy R nu qTarget
        cert.generalization.q lam := by
  -- the certified net decrease
  set dec : ℝ := cert.merge.gap + cert.joint.eta
      * cert.joint.inner - cert.joint.lip * cert.joint.eta
      * cert.joint.eta * cert.joint.dnorm2 / 2
      - cert.compress.kappa * cert.compress.qerr with hdec
  -- energy bookkeeping: E' <= E0 - dec
  have hE : cert.compress.energy ≤ cert.grow.preEnergy - dec := by
    have h1 := cert.compress.hslack
    have h2 := cert.joint.hquad
    have h3 := cert.merge.hdrop
    have h4 := cert.grow.hdrop
    rw [cert.chain_jc] at h1
    rw [cert.chain_mj] at h2
    rw [cert.chain_gm] at h3
    linarith [cert.grow.hgain]
  -- penalty bookkeeping (multiplicative wrap: nu*M'
  -- is an atom, so lift the bound through nu >= 0)
  have hpen := penalty_drop_bound qTarget
    cert.generalization.q cert.generalization.q'
    cert.generalization.epsQ cert.generalization.heps
    cert.generalization.hdrop
  have hnuM : nu * max 0 (qTarget - cert.generalization.q')
      ≤ nu * max 0 (qTarget - cert.generalization.q)
        + nu * cert.generalization.epsQ :=
    calc nu * max 0 (qTarget - cert.generalization.q')
        ≤ nu * (max 0 (qTarget - cert.generalization.q)
          + cert.generalization.epsQ) :=
          mul_le_mul_of_nonneg_left hpen hnu
    _ = nu * max 0 (qTarget - cert.generalization.q)
        + nu * cert.generalization.epsQ := by ring
  -- combine (all products are atoms now; pure linear algebra)
  unfold hagiPotential Hagi.Foundations.hagiPotential
  have hs : lam * (R + cert.grow.risk + cert.merge.risk
      + cert.joint.risk) = lam * R
      + lam * (cert.grow.risk + cert.merge.risk
        + cert.joint.risk) := by ring
  rw [hs]
  linarith [hE, hnuM, hprice, hdec]

end Hagi.System
