/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Hadamard
import Hagi.Core.FrobOuter
import Hagi.Core.Kronecker
import Hagi.Core.BlockDiag
import Hagi.Core.Merge
import Hagi.Energy.Ternary
import Hagi.Energy.Quantizer
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
import Hagi.Core.RealF3Ortho
import Hagi.Core.Element
import Hagi.Step.Joint
import Hagi.Step.MuonAlign
import Hagi.Step.Compound
import Hagi.Budget.RankBudget
import Hagi.Data.DField
import Hagi.Data.DataMixing
import Hagi.Data.InfoNCE
import Hagi.Step.NCEExact
import Hagi.Step.LazyAdam
import Hagi.Budget.BatchCap
import Hagi.Data.DFieldKKT
import Hagi.Data.DBridge
import Hagi.Data.Distill
import Hagi.Data.DistillRecursion
import Hagi.Data.CertifiedArgmax
import Hagi.Step.SafeQP
import Hagi.Step.ProjectionDescent
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
import Hagi.Energy.EntropyProduction
import Hagi.Autonomy.SupervisorViability
import Hagi.Runtime.ControllerGates
import Hagi.Budget.BitAlloc
import Hagi.Budget.BitAllocTermination
import Hagi.Data.NessDissipation
import Hagi.Probability.StationaryFlatness
import Hagi.Data.FannesSmooth
import Hagi.Budget.WaterFilling
import Hagi.Pretraining.Dust
import Hagi.Pretraining.ProbeError
import Hagi.Pretraining.RobustnessLaw
import Hagi.Pretraining.Grokking
import Hagi.Pretraining.DataPruning
import Hagi.Pretraining.DustAlign
import Hagi.Omni.CrossModalGap
import Hagi.Omni.SharedStateComposition
import Hagi.Omni.TemporalState
import Hagi.Omni.OmniInvariant
import Hagi.Omni.CapabilityMatrix
import Hagi.Prelude.Info
import Hagi.Foundations.GrowthDynamics
import Hagi.Foundations.StageCalculus
import Hagi.Information.DiscreteFannes
import Hagi.Unified.InfoDataCore
import Hagi.Unified.CostComposition
import Hagi.Unified.DynamicsGrowthCore
import Hagi.Unified.BudgetCore
import Hagi.Unified.CoreFacades
import Hagi.Unified.AlgebraMatrixCore
import Hagi.Unified.GrowthEnsembleCore
import Hagi.Unified.PretrainOptRobustCore
import Hagi.Unified.StepLaws
import Hagi.Unified.StepExt
import Hagi.Information.MemoryCapacity
import Hagi.Information.Pinsker
import Hagi.Information.GainRecoverability
import Hagi.Information.RoutingCapacity
import Hagi.Growth.AdaptiveQuery
import Hagi.Probability.KLSBridge
import Hagi.Probability.ThermoBridge
import Hagi.Step.KLSSafeQP
import Hagi.Architecture.CortexFiber
import Hagi.Architecture.AlignedMerge
import Hagi.Architecture.OrthoInjection
import Hagi.Architecture.Heterarchy
import Hagi.Architecture.ConfigurationCost
import Hagi.Budget.ActiveCompute
import Hagi.Architecture.ConfigurationRouting
import Hagi.Budget.FlopsEconomy
import Hagi.Budget.WaterFillingMoE
import Hagi.Architecture.ResidualSplit
import Hagi.Budget.TokenWeightBias
import Hagi.Ensemble.MergeScaling
import Hagi.Core.F3Root
import Hagi.Energy.PreNorm
import Hagi.Budget.DesignOpt
import Hagi.Energy.Variational
import Hagi.Energy.Cooling
import Hagi.Energy.PoEBound
import Hagi.Step.Upgrades
import Hagi.External.Diversity
import Hagi.External.MemT.GDN2
import Hagi.External.Flywheel.NormSupport
import Hagi.External.Flywheel.FrobeniusNorm
import Hagi.External.Flywheel.TruncatedSVDRank1
import Hagi.External.Flywheel.MatrixNormRelations
import Hagi.External.Flywheel.SpectralNormGap
import Hagi.External.Flywheel.CoherenceCharacterization
import Hagi.External.Flywheel.MDLRank
import Hagi.Audit.Exactness
import Hagi.Core.RootContrast
import Hagi.Audit.EqualBudget
import Hagi.Unified.Unified
import Hagi.Unified.RecursiveGrowth
import Hagi.Dynamics.EndpointContraction
import Hagi.Dynamics.SpeedLimit
import Hagi.Dynamics.UrgencyDepth
import Hagi.Dynamics.DistillationRate
import Hagi.Autonomy.TTTStability
import Hagi.Autonomy.Hedge
import Hagi.Autonomy.HedgeSurvivor
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
import Hagi.Probability.FreedmanTwoSided
import Hagi.Probability.Azuma
import Hagi.Probability.Freedman
import Hagi.Probability.NoiseTemperature
import Hagi.Probability.ThermoAxes
import Hagi.Probability.GibbsConcentration
import Hagi.Probability.MWU
import Hagi.Probability.WSqD
import Hagi.Growth.RecursiveSelfDevelopment
import Hagi.Growth.RatioTakeoff
import Hagi.Growth.Saturation
import Hagi.Growth.GrowthCeiling
import Hagi.Dynamics.ProxyGap
import Hagi.Growth.PlasticityLedger
import Hagi.Growth.TakeoffElasticity
import Hagi.Ensemble.CompressionCert
import Hagi.Unified.MasterHAGITrunc
import Hagi.Model.SoftmaxStep
import Hagi.Model.HypothesisCompetition
import Hagi.Foundations.Recurrence
import Hagi.Foundations.SumIdentities
import Hagi.Foundations.GrowthBand
import Hagi.Foundations.Telescope
import Hagi.Foundations.ConeTakeoff
import Hagi.Foundations.PerronCone
import Hagi.Foundations.MesoScale
import Hagi.Foundations.ConeCorridor
import Hagi.Unified.QuantizedCone
import Hagi.Budget.CertifiedArgmax
import Hagi.Ensemble.SigmaKernel
import Hagi.Growth.RsiCriterion
import Hagi.Architecture.FactorRank
import Hagi.Growth.GainDecomposition
import Hagi.Growth.DisagreementChain
import Hagi.Growth.ChainToCone
import Hagi.Growth.ChainUnification
import Hagi.Growth.T3Ignition
import Hagi.Growth.NonlinearCone
import Hagi.Growth.NoiseDisentangle
import Hagi.Growth.ConeDynamics
import Hagi.Growth.FiberNecessity
import Hagi.Growth.IntegrationOrder
import Hagi.Growth.RoundViability
import Hagi.Growth.GainCeiling
import Hagi.Step.GPM
import Hagi.Ensemble.MergePrice
import Hagi.Ensemble.PolicyCompatibility
import Hagi.Ensemble.MergeMixture
import Hagi.Core.NonlinearStep0
import Hagi.Unified.ArchitectureTheorem
import Hagi.Examples.HAGICertWitness
import Hagi.Examples.QuadraticConcrete
import Hagi.Core.RoPEMoments
import Hagi.Step.CausalFilter
import Hagi.Ensemble.QFormerBridge
import Hagi.Step.Muon
import Hagi.Step.MuonWD
import Hagi.Step.MuonTwoLevel
import Hagi.Step.HybridState
import Hagi.Step.SNRWeights
import Hagi.Autonomy.SupervisorSafety
import Hagi.Discovery.PPT
import Hagi.Pretraining.SyntheticPretrain
import Hagi.Sparsity.SparseStep0
import Hagi.System.GrowthState
import Hagi.System.StepCertificate
import Hagi.System.GrowthStateViews
import Hagi.Unified.GrowthBridge
import Hagi.Unified.AnytimeMartingale
import Hagi.Unified.TopLevel
import Hagi.Energy.STEStep
import Hagi.Runtime.TernaryExact
import Hagi.Step.JointPreserve
import Hagi.Budget.ElementQuant
import Hagi.Step.LazyAdamMomentum
import Hagi.Budget.JointCost
import Hagi.Growth.SeedOnly
import Hagi.Spectral.RankGrowth
import Hagi.Architecture.FactorizedMerge
import Hagi.Generalization.ModeState
import Hagi.Unified.MasterHAGI
import Hagi.Challenge.MasterChallenge
import Hagi.Unified.CorePremisesDerived
import Hagi.Unified.MasterHAGICoupled
import Hagi.Unified.LinkedWitness
import Hagi.Unified.LearningKernel
import Hagi.Unified.GrandSynthesis
import Hagi.System.Certificates
import Hagi.System.DiscreteStep
import Hagi.System.UnifiedStep
import Hagi.Examples.Nonvacuity
import Hagi.Unified.Assumptions
import Hagi.Unified.StateTakeoff
import Hagi.Architecture.LiveDelta
import Hagi.Runtime.LiveDeltaQuant
import Hagi.Step.LiveDeltaSafe
import Hagi.Growth.Thermostat
import Hagi.Unified.MemoryCycle
import Hagi.Unified.QuantSafeUpdate
import Hagi.Unified.LiveDeltaCycle
import Hagi.Probability.PMFBridge
import Hagi.Probability.BernoulliFactory
import Hagi.Step.MDLObjective
import Hagi.Step.MDLThreeCurrency
import Hagi.Step.WarmupSchedule
import Hagi.Step.WeightDecay
import Hagi.Step.NewtonPolar
import Hagi.Step.RiemannNewtonPolar
import Hagi.Step.FrobeniusLMO
import Hagi.Step.PreconditionerDescent
import Hagi.Step.MetricSafeQP
import Hagi.Step.ArmijoAcceptance
import Hagi.Budget.AnytimeCondensation
import Hagi.Budget.ThermoCondensation
import Hagi.External.Flywheel.CourantFischer
import Hagi.External.Flywheel.SVD
import Hagi.External.Flywheel.WeylInequality
import Hagi.Foundations.Chord
import Hagi.Foundations.Hoeffding
import Hagi.Foundations.Ortho
import Hagi.Foundations.Potential
import Hagi.Growth.GammaDeficit
import Hagi.Probability.ChernoffCGF
import Hagi.Probability.EntropyConvexity
import Hagi.Probability.ExpChord
import Hagi.Probability.GibbsCooling
import Hagi.Probability.GibbsInfoCore
import Hagi.Probability.MomentBounds
import Hagi.Probability.PinskerTV
import Hagi.Probability.SphericalAngle
import Hagi.Unified.CertifiedGrowth
import Hagi.Unified.DerivAlong
import Hagi.Unified.AdvanceWitness
import Hagi.Examples.EdgeTests
import Hagi.Unified.FannesComplete
import Hagi.Unified.GaugeQuotient
import Hagi.Unified.InterpretiveGrowth
import Hagi.Unified.ModelComparison
import Hagi.Unified.NernstFannes
import Hagi.Examples.NonvacuityHorizon
import Hagi.Unified.RecursiveClean
import Hagi.Model.StageSemantics
import Hagi.Model.CertifiedTransition
import Hagi.Model.CycleCertificate
import Hagi.Model.ModernHopfield
import Hagi.Model.ReferenceMachine
import Hagi.Model.MachineBridge
import Hagi.Model.ModeConnectivity
import Hagi.Model.MuPScaling
import Hagi.Model.ComputeOptimal
import Hagi.Model.LayerNorm
import Hagi.Model.RMSNorm
import Hagi.Model.SwiGLU
import Hagi.Model.Speculative
import Hagi.Model.DPO
import Hagi.Model.GRPO
import Hagi.Model.SwitchMoE
import Hagi.Model.LoRA
import Hagi.Model.QKNorm
import Hagi.Model.HNet
import Hagi.Model.MambaSSM
import Hagi.Model.DDPM
import Hagi.Model.CFG
import Hagi.Model.FlowMatching
import Hagi.Model.MLA
import Hagi.Model.GQA
import Hagi.Model.ALiBi
import Hagi.Model.StreamingLLM
import Hagi.Model.GDNRAM
import Hagi.Model.FlashAttention
import Hagi.Model.MoD
import Hagi.Model.Perceiver
import Hagi.Model.PreNorm
import Hagi.Model.ReZero
import Hagi.Model.LogitPSV
import Hagi.Unified.StepContract
import Hagi.Unified.AnytimePACBayes
import Hagi.Model.MeasurementCert
import Hagi.Unified.CertifiedTrajectory
import Hagi.Model.ModelSoup
import Hagi.Model.LabelSmoothing
import Hagi.Optimization.Lookahead
import Hagi.Model.LookaheadTrajectory
import Hagi.Probability.BatchSNR
import Hagi.Examples.QuadraticEndToEnd
import Hagi.Model.MeasuredEffects
import Hagi.Model.SourceMixture
import Hagi.Model.SWA
import Hagi.Model.ZLoss
import Hagi.Model.Matryoshka
import Hagi.Model.Softcap
import Hagi.Optimization.AdamBias
import Hagi.Optimization.AdamW
import Hagi.Optimization.GradAccum
import Hagi.Optimization.LLRD
import Hagi.Optimization.PPOClip
import Hagi.Step.GradClip
import Hagi.Unified.MicroStepCert
import Hagi.Model.Residual
import Hagi.Model.RoPE
import Hagi.Unified.Distillation
import Hagi.Model.Sidon
import Hagi.Optimization.SphericalDamping
import Hagi.Optimization.InexactContraction
import Hagi.Optimization.RobbinsMonro
import Hagi.Optimization.MirrorDescent
import Hagi.Numerics.SoftmaxFix
import Hagi.Planning.Imagination
import Hagi.Geometry.SphericalSimplex
import Hagi.Ensemble.UniformCert
import Hagi.Model.MoeExpansion
import Hagi.Model.MemoryConsolidation
import Hagi.Model.ConsolidationMirror
import Hagi.Optimization.Momentum
import Hagi.Optimization.ComputeScaling
import Hagi.Optimization.PLConvergence
import Hagi.Optimization.NeuronAlloc
import Hagi.Optimization.LRSchedule
import Hagi.Optimization.PolyStep
import Hagi.Optimization.DREAM
import Hagi.Optimization.SubspaceGrowth
import Hagi.Optimization.AdaptiveCycle
import Hagi.Optimization.DirectionPacking
import Hagi.Energy.Landauer
import Hagi.Pretraining.Speedrun
import Hagi.Pretraining.TrustRegion
import Hagi.Percolation.Site

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