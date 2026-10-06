/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Hadamard
import Hagi.Core.Kronecker
import Hagi.Core.DFT3
import Hagi.Core.BlockDiag
import Hagi.Core.Merge
import Hagi.Energy.Ternary
import Hagi.Core.ErrorProp
import Hagi.Core.Attention
import Hagi.Core.Lift
import Hagi.Core.Concat
import Hagi.Core.Ridge
import Hagi.Core.Select
import Hagi.Core.Mix
import Hagi.Budget.KVWater
import Hagi.Core.Ambig
import Hagi.Growth.Grow
import Hagi.Ensemble.GapLaw
import Hagi.Ensemble.Hoeffding
import Hagi.Core.RealF3
import Hagi.Core.RealF3Ortho
import Hagi.Core.Element
import Hagi.Step.Joint
import Hagi.Ensemble.GenCycle
import Hagi.Step.Compound
import Hagi.Budget.RankBudget
import Hagi.Step.NCE
import Hagi.Step.NCEVar
import Hagi.Data.DField
import Hagi.Data.ValueOfRead
import Hagi.Step.NCEExact
import Hagi.Step.LazyAdam
import Hagi.Budget.ComputeBudget
import Hagi.Data.DFieldKKT
import Hagi.Data.DBridge
import Hagi.Data.Distill
import Hagi.Data.DistillRecursion
import Hagi.Step.SafeQP
import Hagi.Step.SafeQPStep
import Hagi.Step.StochasticSafeQP
import Hagi.Step.AdaptiveSafeQP
import Hagi.Step.Dominate
import Hagi.Step.Decompose
import Hagi.Energy.FreeEnergy
import Hagi.Growth.GrowthGate
import Hagi.Growth.GainRenewal
import Hagi.Growth.FrontierScaling
import Hagi.Ensemble.MergeIdentity
import Hagi.Energy.BranchScale
import Hagi.Energy.TernaryLean
import Hagi.Energy.EntropyProduction
import Hagi.Autonomy.SupervisorViability
import Hagi.Unified.MacroCycleV2
import Hagi.Budget.BitAlloc
import Hagi.Data.NessDissipation
import Hagi.Probability.StationaryFlatness
import Hagi.Data.FannesSmooth
import Hagi.Budget.WaterFilling
import Hagi.Pretraining.Dust
import Hagi.Probability.KLSBridge
import Hagi.Step.KLSSafeQP
import Hagi.Architecture.CortexFiber
import Hagi.Ensemble.MergeScaling
import Hagi.Depth.F3Root
import Hagi.Data.SinkCost
import Hagi.Energy.PreNorm
import Hagi.Budget.DesignOpt
import Hagi.Energy.Variational
import Hagi.Energy.PoEBound
import Hagi.Step.Upgrades
import Hagi.External.Diversity
import Hagi.External.Transport
import Hagi.External.Transfer
import Hagi.Audit.Foundations
import Hagi.Audit.Optimality
import Hagi.Audit.Exactness
import Hagi.External.Layers
import Hagi.Depth.RootContrast
import Hagi.Growth.CycleChannel
import Hagi.Audit.EqualBudget
import Hagi.Unified.Unified
import Hagi.Unified.GlobalConvergence
import Hagi.Unified.MacroCycle
import Hagi.Unified.RecursiveGrowth
import Hagi.Dynamics.CurvatureSafe
import Hagi.Dynamics.Contraction
import Hagi.Autonomy.TTTStability
import Hagi.Autonomy.Hedge
import Hagi.Data.PACBayes
import Hagi.Autonomy.Insight
import Hagi.Unified.Liveness
import Hagi.Dynamics.CapabilityGain
import Hagi.Dynamics.FastGrowth
import Hagi.Dynamics.WallClockTakeoff
import Hagi.Dynamics.ControllerPolicy
import Hagi.Probability.ConditionalSuccess
import Hagi.Probability.CertifiedEstimator
import Hagi.Growth.FrontierProduction
import Hagi.Growth.SelfDevelopment
import Hagi.Growth.StateBinding
import Hagi.Autonomy.ParetoController
import Hagi.Probability.AdaptiveSuccess
import Hagi.Probability.Azuma
import Hagi.Probability.Freedman
import Hagi.Probability.NoiseTemperature
import Hagi.Growth.RecursiveSelfDevelopment
import Hagi.Growth.RatioTakeoff
import Hagi.Growth.Saturation
import Hagi.Growth.GrowthCeiling
import Hagi.Deployment.ProxyGap
import Hagi.Growth.PlasticityLedger
import Hagi.Growth.TakeoffElasticity
import Hagi.Ensemble.CompressionCert
import Hagi.Data.BinEntMono
import Hagi.Unified.MasterHAGITrunc
import Hagi.Model.SoftmaxStep
import Hagi.Foundations.Recurrence
import Hagi.Foundations.Telescope
import Hagi.Foundations.ConeTakeoff
import Hagi.Budget.CertifiedArgmax
import Hagi.Ensemble.SigmaKernel
import Hagi.Growth.RsiCriterion
import Hagi.Growth.StateClosedRenewal
import Hagi.Architecture.FactorRank
import Hagi.Ensemble.MergeCancellation
import Hagi.Growth.GainOperator
import Hagi.Step.GPM
import Hagi.Ensemble.MergePrice
import Hagi.Core.NonlinearStep0
import Hagi.Ensemble.DistillTransfer
import Hagi.Ensemble.RecursiveDistill
import Hagi.Step.SafeQPPL
import Hagi.Data.AntiCollapse
import Hagi.Autonomy.Universality
import Hagi.Unified.ArchitectureTheorem
import Hagi.Core.RoPE
import Hagi.Core.GQA
import Hagi.Core.SWA
import Hagi.Step.CausalFilter
import Hagi.Data.PuncturedCE
import Hagi.Ensemble.QFormerBridge
import Hagi.Data.ChunkedCE
import Hagi.Step.LRWidth
import Hagi.Step.Muon
import Hagi.Data.TernaryChinchilla
import Hagi.Autonomy.SupervisorSafety
import Hagi.Discovery.PPT
import Hagi.Pretraining.SyntheticPretrain
import Hagi.Sparsity.SparseStep0
import Hagi.Unified.GrowthState
import Hagi.Unified.GrowthBridge
import Hagi.Unified.AnytimeValid
import Hagi.Unified.AnytimeMartingale
import Hagi.Unified.TopLevel
import Hagi.Unified.GlobalDynamics
import Hagi.Energy.STEStep
import Hagi.Energy.QuantBridge
import Hagi.Runtime.TernaryExact
import Hagi.Step.JointPreserve
import Hagi.Budget.ElementQuant
import Hagi.Step.LazyAdamMomentum
import Hagi.Step.SafeQPRobust
import Hagi.Budget.JointCost
import Hagi.Growth.SeedOnly
import Hagi.Spectral.SpectralProjector
import Hagi.Architecture.FactorizedMerge
import Hagi.Generalization.ModeState
import Hagi.Unified.MasterHAGI

set_option linter.style.header false

/-!
# Formalization of HAGI_v2

This library formalizes the mathematical core of the HAGI_v2 project
(E:/HAGI_v2) — a "ternary RD-channel causal language model" grown from
small domain experts instead of being trained from scratch.

The modules correspond to the mathematical constructions of the project:

* `Hagi.Core/Hadamard` — the Sylvester (Walsh) Hadamard matrices `H_n / √n`
  used by the Hadamard cross-expert mixer (`src/hagi/model/merge.py`,
  GROWING_HYPOTHESIS.md, Part V). Orthonormality: `H * Hᵀ = n • 1`.
* `Hagi.Core/Kronecker` — the Kronecker product `⊗ₖ` preserves
  (conjugate-)orthonormality; underlies the recursive/local Hadamard
  mixer `Q = H_{g_k} ⊗ ⋯ ⊗ H_{g_1}` (GROWING_HYPOTHESIS.md, Part VI)
  and the DFT-3 Kronecker recursion `F₃ᵏ`.
* `Hagi.Core/DFT3` — the ternary DFT-3 (F₃) mixer of the recursive ternary
  growth cycle (README.md "Growth cycle algorithm"): `F₃` is unitary,
  every entry has modulus `1/√3`, and the Kronecker powers `F₃ᵏ` are
  unitary — "uniform mixing with no blind channels".
* `Hagi.Core/BlockDiag` — block-diagonal merge: at step 0 the merged model
  computes *exactly* the N independent experts
  (GROWING_HYPOTHESIS.md "Механизм", `src/hagi/model/merge.py`).
* `Hagi.Core/Merge` — step-0 equivalence of the mixer merge: with the head
  pre-rotation `W' = W * Qᵀ`, the mixer path `W' *ᵥ (Q *ᵥ x) = W *ᵥ x`;
  the concat head sums the experts' logits (the `logit_scale / √N`
  observation); an orthonormal mixer preserves the inner product —
  it is information-neutral.
* `Hagi.Energy/Ternary` — ternary quantization (`dsv4_experts.py`,
  `dsv4_refit_experts.py`): 5 trits pack injectively into a byte
  (`3⁵ = 243 ≤ 256`), and nearest-grid rounding on the ternary
  `{-1, 0, +1}` / int4 `±7` grids has error at most half a step.
* `Hagi.Core/ErrorProp` — the telescopic error-accumulation law of the
  sequential compression pass: `δ_{l+1} = J_l δ_l + r_l` with
  Lipschitz `‖J_l‖ ≤ α` gives `‖δ_L‖ ≤ α^L ‖δ₀‖ + ρ Σ αⁱ`; for the
  measured `α ≤ 1` this is the Σ-accumulation of expected error
  (README.md "telescopic fitting").
* `Hagi.Core/Attention` — softmax-weighted error damping: an error `eᵢ`
  entering the attention output weighted by `pᵢ` contributes at most
  `max ‖eᵢ‖` — the principle behind the KV precision pyramid
  (README.md "Target KV design").

* `Hagi.Core/Lift` — the parent-preserving ternary lift `Q(π/2)` of the
  recursive F3 tree (`ParentPreservingTernaryLift`, commit series
  2026-09-27): orthogonal, fixes the diagonal `(1,1,1)` pointwise —
  "lifting three identical parent copies is the identity on their
  diagonal", the property that makes tree depth meaningful; the leaf
  subspace is invariant; the root-mode cortex preserves leaf
  equality (ARCHITECTURE_V2).
* `Hagi.Core/Concat` — the concat==child invariant and the temperature
  correction (commit `74e7d30`, `test_merge_invariants.py`): the
  concat head of N identical children sums the block contributions
  (`n • (W *ᵥ x)`), the identity scale is forced to be `1/n` (the
  `logit_scale = child/n` fix), and rescaled logits reproduce the
  softmax only on constant logits — a CE change from a temperature
  rescale is an artifact, not a quality gain.

Empirical measurements (RMS errors, benchmark scores, saturation
curves) are not mathematical statements and are intentionally out of
scope.
-/
