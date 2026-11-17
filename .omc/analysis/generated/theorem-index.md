# Theorem index (generated)

GENERATED - do not edit. Regenerate with
`python scripts/GenTheoremIndex.py` (runs a Lean environment
census, a fresh AssumptionScan scan, and the typed premise
registry).

Per-module theorem/def counts, noncomputable declarations,
premise status (Proven|Conditional|Empirical|Speculative|
Deprecated), and the global axiom profile of all Hagi.*
theorems.

## Summary

- modules: 610
- theorems: 11273
- defs: 3618
- noncomputable decls: 1076
- status Proven: 532 modules
- status Conditional: 23 modules
- status Empirical: 11 modules
- status Speculative: 24 modules
- status Deprecated: 20 modules
- global axioms of all Hagi.* theorems: Classical.choice, Quot.sound, propext (OK)

## Per-module index

| module | theorems | defs | noncomputable | premises | status |
|---|---|---|---|---|---|
| Hagi | 0 | 0 | - | no | Proven |
| Hagi.Architecture.AlignedMerge | 5 | 1 | - | no | Proven |
| Hagi.Architecture.CascadeLeak | 13 | 1 | - | no | Proven |
| Hagi.Architecture.Configuration | 3 | 0 | - | no | Proven |
| Hagi.Architecture.CortexFiber | 5 | 1 | - | no | Proven |
| Hagi.Architecture.FactorRank | 6 | 5 | nonnegRank | no | Proven |
| Hagi.Architecture.FactorizedMerge | 11 | 3 | fullMerge, meanResidual | no | Proven |
| Hagi.Architecture.Heterarchy | 3 | 2 | - | no | Proven |
| Hagi.Architecture.IsoFrobCascade | 33 | 3 | isoFrobEnergy, isoCascadeEnergy | no | Proven |
| Hagi.Architecture.LiveDelta | 9 | 16 | - | no | Proven |
| Hagi.Architecture.ManifoldHyperConn | 3 | 2 | - | no | Proven |
| Hagi.Architecture.OrthoInjection | 5 | 0 | - | no | Proven |
| Hagi.Architecture.ResidualSplit | 9 | 6 | - | no | Proven |
| Hagi.Architecture.SpaceDecoupling | 9 | 2 | - | no | Proven |
| Hagi.Audit.Audit | 63 | 0 | - | no | Proven |
| Hagi.Autonomy.Insight | 10 | 1 | scalarQuadraticKl | yes | Empirical |
| Hagi.Autonomy.ParetoController | 15 | 1 | dirTau | no | Proven |
| Hagi.Autonomy.SupervisorSafety | 20 | 37 | capMember | no | Proven |
| Hagi.Autonomy.SupervisorViability | 30 | 14 | LittlestoneDim | no | Proven |
| Hagi.Autonomy.TTTStability | 2 | 0 | - | no | Proven |
| Hagi.Benchmarks | 0 | 0 | - | no | Proven |
| Hagi.Benchmarks.QuadLoopWitness | 24 | 2 | qhalf, halfStepCert | no | Proven |
| Hagi.Benchmarks.QuadraticEndToEnd | 8 | 4 | qQuantized | no | Proven |
| Hagi.Benchmarks.QuarticWitness | 29 | 12 | qFloor, w2, qDrops, qCert1, w0, qMeasured, qTraj, qBud, qE, w1, qCert2 | no | Proven |
| Hagi.Benchmarks.TernaryWitness | 7 | 3 | ternaryStepCert, quant_jump_honest, quantOpt | no | Proven |
| Hagi.Budget.ActiveCompute | 3 | 0 | - | no | Proven |
| Hagi.Budget.AnytimeCondensation | 3 | 0 | - | no | Proven |
| Hagi.Budget.BatchCap | 23 | 3 | batchEff, criticalS, sfoCost | no | Proven |
| Hagi.Budget.BitAlloc | 52 | 3 | layerError, totalError, totalErrorCont | no | Proven |
| Hagi.Budget.BitAllocTermination | 7 | 0 | - | no | Proven |
| Hagi.Budget.DesignOpt | 6 | 1 | wallClock | no | Proven |
| Hagi.Budget.ElementQuant | 4 | 0 | - | no | Proven |
| Hagi.Budget.FlopsEconomy | 2 | 0 | - | no | Proven |
| Hagi.Budget.IsoFrobAlloc | 2 | 1 | isoFrobSensitivity | no | Proven |
| Hagi.Budget.JointCost | 6 | 1 | nsIter | no | Proven |
| Hagi.Budget.KVWater | 2 | 1 | kvResidual | no | Proven |
| Hagi.Budget.RDAlloc | 14 | 15 | rdAllocBytes, rd_step_certified | no | Proven |
| Hagi.Budget.RankBudget | 16 | 1 | rankResidual | no | Proven |
| Hagi.Budget.ResidualVQ | 15 | 1 | - | no | Proven |
| Hagi.Budget.ThermoCondensation | 38 | 3 | log2_3, bpw, factorizedTernaryBits | no | Proven |
| Hagi.Budget.TokenWeightBias | 2 | 0 | - | no | Proven |
| Hagi.Budget.WaterFilling | 3 | 1 | totalErrorFin | no | Proven |
| Hagi.Budget.WaterFillingMoE | 10 | 2 | effectiveCapacity, genMean | no | Proven |
| Hagi.Budget.WeightedExpAlloc | 22 | 4 | weightedExpBudget, weightedExpPrice, weightedExpLogCoeff, weightedExpAllocation | no | Proven |
| Hagi.Cert.Adapters | 4 | 3 | - | yes | Conditional |
| Hagi.Cert.CertifiedArgmax | 11 | 3 | avgRadius | no | Proven |
| Hagi.Cert.Core | 50 | 79 | - | no | Proven |
| Hagi.Cert.Empirical | 5 | 13 | - | no | Proven |
| Hagi.Cert.StepGen | 61 | 36 | - | no | Proven |
| Hagi.Challenge.MasterChallengeV3 | 1 | 0 | - | no | Proven |
| Hagi.Challenge.MasterChallengeV4Kernel | 1 | 0 | - | no | Proven |
| Hagi.Contracts.AuditLedger | 50 | 40 | - | no | Proven |
| Hagi.Contracts.BatchCEAlignmentBudget | 30 | 2 | fixedAlignmentCesaro, rangeCurvature | no | Proven |
| Hagi.Contracts.BatchCEBestResidual | 4 | 0 | - | no | Proven |
| Hagi.Contracts.BatchCEBudgetAsym | 38 | 4 | asymmetricPairMinimumNormBatchStep, asymmetricMeanBatchStep | no | Proven |
| Hagi.Contracts.BatchCEBudgetExpanded | 18 | 6 | expandedTrainState, batchCEMeasured, evaluatedBatchMinimumNormCert, batchMinimumNormMinimalCert, expandedHalfTrainStep | no | Proven |
| Hagi.Contracts.BatchCEBudgetGuard | 26 | 3 | batchSampleCE, guardedBatchTrainStep, batchDirectionTrainStep | no | Proven |
| Hagi.Contracts.BatchCEBudgetHalf | 20 | 3 | batchDirectionHalfTrainInput, batchDirectionHalfTrainStep, batchMinimumNormTrainStep | no | Proven |
| Hagi.Contracts.BatchCEBudgetIdentity | 44 | 14 | batchParetoProblemSafeDecidable, identityParetoBatchStep, batchParetoProblem, pairMinimumNormBatchParetoProblemSafeDecidable, batchParetoStepFun, guardedBatchParetoStepFun, guardedBatchParetoProblemSafeDecidable, pairMinimumNormBatchParetoProblem, minimumNormBatchParetoProblem, minimumNormBatchParetoProblemSafeDecidable, guardedBatchParetoProblem, identityMinimumNormBatchStep | no | Proven |
| Hagi.Contracts.BatchCEBudgetPareto | 17 | 2 | batchPairMinimumNormTrainStep, budgetedParetoBatchTrainStep | no | Proven |
| Hagi.Contracts.BatchCEGrowth | 108 | 58 | residualDirection, residualAdmissionMargin, residualStepMargin, residualFeatures, grownBatchState, quarantinedGrowStep, growthObjective, residualPath, growthPath, boundedGrowStep | no | Proven |
| Hagi.Contracts.BatchCEGrowthSelection | 94 | 23 | growthAdmissionProblemAt_decidable_safe, growthAdmissionPlanStep, growthCandidateOperationIncrement, growthAdmissionMemoryIncrement, growthCandidateStep, smoothedGrowthYield, growthSelection, growthAdmissionPlanRollout, growthAdmissionPlanSelection, growthProblemAt, growthAdmissionOperationIncrement, growthAdmissionSelectionTrace, growthAdmissionSelection, growthAdmissionSelectionPath, growthAdmissionPlanProblemAt, growthAdmissionSelectionNext, growthAdmissionPlanProblemAt_decidable_safe, growthProblemAt_decidable_safe, growthSelectionNext, growthCandidateMemoryIncrement, growthAdmissionProblemAt | no | Proven |
| Hagi.Contracts.BatchCEStepCertificate | 0 | 0 | - | no | Proven |
| Hagi.Contracts.BatchCEStepCore | 47 | 13 | heterogeneousStepCert, batchDirectionTrainInput, batchPairMinimumNormTrainInput, batchTrainStepCert, batchTrainStepMinimalCert, batchCEObjective, batchTrainInput, batchTrainStep, batchLogitCertifiedDrop, batchMinimumNormTrainInput, batchCertifiedDrop, heterogeneousStep | no | Proven |
| Hagi.Contracts.BatchCETrajectory | 0 | 0 | - | no | Proven |
| Hagi.Contracts.BatchCETrajectoryCanonical | 17 | 0 | - | no | Proven |
| Hagi.Contracts.BatchCETrajectoryDirection | 23 | 0 | - | no | Proven |
| Hagi.Contracts.BatchCETrajectoryEvaluated | 8 | 0 | - | no | Proven |
| Hagi.Contracts.BatchCETrajectoryFixedBatch | 13 | 5 | fixedBatchState, fixedBatchObjective | no | Proven |
| Hagi.Contracts.BatchCETrajectoryFixtures | 15 | 6 | identityScaledBatchCEPath, sameZeroInitialMeanDrop, minimumNormIdentityScaledThreshold, minimumNormIdentityInitialMeanDrop, identityMinimumNormScaledBatchCEPath, sameZeroScaledThreshold | no | Proven |
| Hagi.Contracts.BatchCETrajectoryGuarded | 19 | 0 | - | no | Proven |
| Hagi.Contracts.BatchCETrajectoryGuardedInput | 13 | 9 | directionBatchObjective, directionBatchSampleCE, directionBatchMargin, directionBatchMeanMargin, guardedBatchInputPath, directionBatchState | no | Proven |
| Hagi.Contracts.BatchCETrajectoryHalfMinNorm | 32 | 6 | directionBatchHalfState, directionBatchMinNormSquaredBudget, directionBatchHalfBindingMargin, directionBatchHalfQuadraticMargin, directionBatchHalfMeanQuadraticMargin | no | Proven |
| Hagi.Contracts.BatchCETrajectoryMinNorm | 17 | 0 | - | no | Proven |
| Hagi.Contracts.BatchRangeBF16Cert | 18 | 3 | batchCEMetrics, batchCE_transitionStep_hold, batchCE_bf16_transitionStep_progress | no | Proven |
| Hagi.Contracts.BudgetedParetoStepCert | 6 | 1 | budgetedParetoStepCert | no | Proven |
| Hagi.Contracts.BudgetedParetoStepContract | 3 | 1 | budgetedParetoStepContract | no | Proven |
| Hagi.Contracts.CEStepCertificate | 36 | 10 | ceTrainInput, batchCEObservation, identityStepCert, identityInitialState, identityCEStep, ceTrainStepCert, ceTrainStep, ceTrainStepMinimalCert, coreCEObjective, coreParameters | no | Proven |
| Hagi.Contracts.ChangingEMTrajectory | 32 | 10 | changingEMPath, changingEMPathDrop, changingEMPathMGain, changingEMPathNLL, currentPosterior, changingEMPathKLResidual | no | Proven |
| Hagi.Contracts.ComputeToQuality | 14 | 1 | totalComputeProduct | no | Proven |
| Hagi.Contracts.CurriculumCert | 7 | 1 | curriculumTotal | no | Proven |
| Hagi.Contracts.DataToQuality | 13 | 1 | sampleComplexity | no | Proven |
| Hagi.Contracts.DepthExitCert | 34 | 27 | d2, d1 | no | Proven |
| Hagi.Contracts.FactorizedMixtureEM | 16 | 4 | mixtureUnitScore, factorizedMixtureLabels, mixtureCurrentPosterior, mixtureVectorBank | no | Proven |
| Hagi.Contracts.FiniteEMTrajectory | 23 | 7 | currentPosterior, finiteEMPathNLL, finiteEMPath | no | Proven |
| Hagi.Contracts.GatePipeline | 25 | 0 | - | no | Proven |
| Hagi.Contracts.GatedCEGradientNorm | 5 | 1 | gatedGrad | no | Proven |
| Hagi.Contracts.GatedCEStepCertificate | 67 | 13 | gatedCEProblemSafeDecidable, identityScaledGatedCEPath, gatedCETrainStepCert, gatedCETrainStep, identityGatedCEStep, gatedCETrainInput, gatedCETrainStepMinimalCert, gatedCEProblem, gatedCEStepFun, gatedCEValueEstimate, budgetedGatedCETrainStep, gatedCEObjective, identityGatedStepCert | no | Proven |
| Hagi.Contracts.GatedCETrajectory | 44 | 7 | fixedGatedAlignment, fixedGatedState, fixedGatedDrop, fixedGatedObjective | no | Proven |
| Hagi.Contracts.GradientBottleneck | 9 | 4 | logitGradRectM, logitGradM | no | Proven |
| Hagi.Contracts.GradientBottleneckIdentification | 15 | 1 | rectangularTail | no | Proven |
| Hagi.Contracts.GuardedLogitTrajectory | 37 | 3 | guardedLogitDrop, guardedLogitProgressCount, guardedLogitPath | no | Proven |
| Hagi.Contracts.HadamardSpread | 20 | 1 | - | no | Proven |
| Hagi.Contracts.HadamardTernaryBridge | 18 | 1 | hadamardImage | no | Proven |
| Hagi.Contracts.IdentityMomentConvergence | 12 | 2 | meanPrediction, empiricalTarget | no | Proven |
| Hagi.Contracts.KVCacheCert | 44 | 27 | lseCombine, tokFull, tokKV, kv_step_certified, tokDen, kvStep, cachedAttn, tokNum | no | Proven |
| Hagi.Contracts.LogicChoiceCert | 31 | 8 | witX, choiceCEMetrics, onesV, choiceCE_transitionStep_progress, witθ, choiceFeatures | no | Proven |
| Hagi.Contracts.LogitGrad | 6 | 1 | logitGrad | no | Proven |
| Hagi.Contracts.MixtureEMTrajectory | 44 | 27 | mixtureState, mixtureGridWeight, mixtureJointMass, mixtureModel, mixtureCanonicalPath, mixtureStateStep, mixtureChannel, mixtureFamily, mixtureTrajectoryModel, mixturePriorMass, mixtureTrajectoryBank | no | Proven |
| Hagi.Contracts.NaturalLean | 0 | 0 | - | no | Proven |
| Hagi.Contracts.ObjectiveTrajectory | 20 | 0 | - | no | Proven |
| Hagi.Contracts.SparseInferenceCert | 28 | 8 | sparse_step_certified | no | Proven |
| Hagi.Contracts.StepCertificate | 8 | 3 | trainStepCert, trainMeasured, trainStepMinimalCert | yes | Conditional |
| Hagi.Contracts.TruncatedSVDTail | 10 | 2 | tailCarrier, approxK | no | Proven |
| Hagi.Contracts.VilleMonitor | 23 | 16 | monitorAnchorQuiet, monitorAnchor | no | Proven |
| Hagi.Core.Ambig | 9 | 0 | - | no | Proven |
| Hagi.Core.Attention | 3 | 0 | - | no | Proven |
| Hagi.Core.BlockDiag | 3 | 1 | - | no | Proven |
| Hagi.Core.Concat | 34 | 4 | lse, ceOneHot, softmaxP | no | Proven |
| Hagi.Core.Element | 6 | 1 | - | no | Proven |
| Hagi.Core.ErrorProp | 20 | 9 | cascadeGain | no | Proven |
| Hagi.Core.F3Root | 3 | 0 | - | no | Proven |
| Hagi.Core.FrobOuter | 3 | 3 | - | no | Proven |
| Hagi.Core.Hadamard | 20 | 4 | hadamardOrthonormal | no | Proven |
| Hagi.Core.Kronecker | 4 | 0 | - | no | Proven |
| Hagi.Core.Lift | 44 | 6 | rootProj, parentPreservingQ, Qentry, mixerQ | no | Proven |
| Hagi.Core.Merge | 4 | 1 | - | no | Proven |
| Hagi.Core.Mix | 1 | 2 | mixedLogits, plainLogits | no | Proven |
| Hagi.Core.NonlinearStep0 | 6 | 5 | - | no | Proven |
| Hagi.Core.RealF3Ortho | 43 | 10 | dftPow, chi3, reUnitMat, reBlock, omega, charMat, reCharMat | no | Proven |
| Hagi.Core.Ridge | 2 | 2 | ridge | no | Proven |
| Hagi.Core.RoPEMoments | 20 | 4 | cosSum, ropeScore, rotVec | no | Proven |
| Hagi.Core.RootContrast | 17 | 4 | rhoCaptured, rootPart, contrastPart, rhoTail | no | Proven |
| Hagi.Core.Select | 8 | 7 | zB, zC, ens, zA | no | Proven |
| Hagi.Data.AnfCompose | 5 | 3 | - | no | Proven |
| Hagi.Data.AnfDispatch | 22 | 21 | - | no | Proven |
| Hagi.Data.AnfTransform | 30 | 9 | - | no | Proven |
| Hagi.Data.BoolVenn | 37 | 15 | signDecode, qAtom, singleAtomCE, worstMask | no | Proven |
| Hagi.Data.BytePatch | 22 | 3 | patchCount, patchSeq | no | Proven |
| Hagi.Data.DBridge | 3 | 1 | negEntropy | no | Proven |
| Hagi.Data.DField | 23 | 12 | divField | no | Proven |
| Hagi.Data.DFieldKKT | 1 | 1 | divField_marginal | no | Proven |
| Hagi.Data.DataMixing | 11 | 1 | mixingLoss | no | Proven |
| Hagi.Data.Distill | 28 | 2 | truncNorm, crossEntropy | no | Proven |
| Hagi.Data.DistillRecursion | 12 | 1 | - | no | Proven |
| Hagi.Data.InfoNCE | 8 | 1 | CE | no | Proven |
| Hagi.Data.NessDissipation | 2 | 3 | flowMap, flowBack, epRate | no | Proven |
| Hagi.Data.PACBayes | 2 | 0 | - | no | Proven |
| Hagi.Deployment.CanaryRamp | 27 | 15 | linearRamp, canary_step_certified | no | Proven |
| Hagi.Dynamics.ControllerPolicy | 2 | 0 | - | no | Proven |
| Hagi.Dynamics.EndpointContraction | 13 | 0 | - | no | Proven |
| Hagi.Dynamics.GrowthBridge | 90 | 12 | ignitionCeiling, ignitionGate, disMean | yes | Speculative |
| Hagi.Dynamics.Laws | 8 | 0 | - | no | Proven |
| Hagi.Dynamics.ProxyGap | 3 | 1 | - | no | Proven |
| Hagi.Energy.EnergyCoordinateStep | 31 | 2 | singleCellFreeEnergy, meanFieldField | no | Proven |
| Hagi.Energy.EnergyFlow | 54 | 2 | localMeanField | no | Proven |
| Hagi.Energy.EntropyProduction | 8 | 4 | entropyProduction | no | Proven |
| Hagi.Energy.FreeEnergy | 4 | 1 | - | no | Proven |
| Hagi.Energy.Landauer | 24 | 1 | landauerUnit | yes | Empirical |
| Hagi.Energy.PairwiseCategorical | 12 | 9 | xtt, pairwiseEnergy, pairwiseInteractionSum, xex, meanFieldFreeEnergy, Bex, expectedPairwiseEnergy, Kex, oneHotState | no | Proven |
| Hagi.Energy.PoEBound | 16 | 1 | smax | no | Proven |
| Hagi.Energy.PreNorm | 5 | 0 | - | no | Proven |
| Hagi.Energy.Quantizer | 30 | 2 | gridQ, gridQVec | no | Proven |
| Hagi.Energy.STEStep | 12 | 1 | tern | yes | Empirical |
| Hagi.Energy.SingleCellDescent | 25 | 6 | transposeLocalField, Bc, localField | no | Proven |
| Hagi.Energy.Ternary | 39 | 4 | roundHalf, roundTern | no | Proven |
| Hagi.Ensemble.CompressionCert | 12 | 16 | deltaCost | no | Proven |
| Hagi.Ensemble.GapLaw | 6 | 2 | twoGap | no | Proven |
| Hagi.Ensemble.Hoeffding | 42 | 0 | - | no | Proven |
| Hagi.Ensemble.MergeIdentity | 9 | 0 | - | no | Proven |
| Hagi.Ensemble.MergeMixture | 2 | 0 | - | no | Proven |
| Hagi.Ensemble.MergePrice | 6 | 3 | sigmaPrice, QuadModel | no | Proven |
| Hagi.Ensemble.MergeScaling | 1 | 0 | - | no | Proven |
| Hagi.Ensemble.PolicyCompatibility | 4 | 2 | integration_net_gain | yes | Conditional |
| Hagi.Ensemble.QFormerBridge | 6 | 2 | - | no | Proven |
| Hagi.Ensemble.SigmaKernel | 5 | 0 | - | no | Proven |
| Hagi.Ensemble.UniformCert | 13 | 0 | - | no | Proven |
| Hagi.External.Diversity | 4 | 0 | - | no | Proven |
| Hagi.External.Flywheel.CoherenceCharacterization | 123 | 16 | kroneckerCoherence, spectralOptimalRank1, spectralGap, effectiveRank, coherenceFactor, kroneckerErrorCoherence, normalizedSingularValueSq | no | Proven |
| Hagi.External.Flywheel.CourantFischer | 117 | 11 | rayleighQuotient, rayleighInf, rayleighSup | no | Proven |
| Hagi.External.Flywheel.EckartYoungLower | 1 | 0 | - | no | Proven |
| Hagi.External.Flywheel.FrobeniusNorm | 31 | 0 | - | no | Proven |
| Hagi.External.Flywheel.MDLRank | 21 | 3 | mdlErr, mdlJ, mdlDj | no | Proven |
| Hagi.External.Flywheel.MatrixNormRelations | 76 | 12 | frobeniusNorm', maxSingularValue, frobeniusNorm'', instCStarAlgebraMatrix, truncatedSVD | no | Proven |
| Hagi.External.Flywheel.NegDiagRank | 2 | 0 | - | no | Proven |
| Hagi.External.Flywheel.NormSupport | 5 | 0 | - | no | Proven |
| Hagi.External.Flywheel.SVD | 0 | 0 | - | no | Proven |
| Hagi.External.Flywheel.SVDCore | 62 | 14 | singularValues, leftSingularVectorExtended, leftSingularVectorNonzero, singularValues₀, onbToMatrix, singularDiagonal, leftUnitary, sqrtConjTransposeMulSelf, constructedU, extendedONB, leftSingularVectorEuclidean, rightUnitary | no | Proven |
| Hagi.External.Flywheel.SVDDiagonal | 8 | 0 | - | no | Proven |
| Hagi.External.Flywheel.SVDEigenvalues | 17 | 0 | - | no | Proven |
| Hagi.External.Flywheel.SVDReal | 45 | 12 | leftSingularVectorExtended_real, realAV, realSingularValues, constructedU_real, leftSingularVectorNonzero_real, onbToMatrix_real, extendedONB_real, rightOrthogonal, singularValues, leftSingularVectorEuclidean_real | no | Proven |
| Hagi.External.Flywheel.SVDRectangular | 34 | 18 | embedMinToM, leftSingularVectorNonzero_rectangular, leftUnitary, embedMinToN, rightUnitary, singularValues, finMinOfAbstract, singularValueFromEigenvalue, eigenvaluesBijection, singularDiagonal | no | Proven |
| Hagi.External.Flywheel.SVDRectangularCoherence | 32 | 4 | coherenceFactorRect, frobeniusNormRect | no | Proven |
| Hagi.External.Flywheel.SVDRectangularDecomposition | 33 | 14 | extendedONB_rectangular, leftSingularVectorEuclidean_rectangular, extendedONB_rectangular_v2, correspondingN, constructedU_rectangular, leftSingularVectorExtended_rectangular, leftSingularVectorByM, diagonalK | no | Proven |
| Hagi.External.Flywheel.SVDRectangularNorms | 15 | 4 | instCStarAlgebraMatrixLocal, maxSingularValue | no | Proven |
| Hagi.External.Flywheel.SVDRectangularOrdering | 15 | 4 | - | no | Proven |
| Hagi.External.Flywheel.SVDTruncated | 17 | 5 | truncatedSVD, truncatedSingularValues, truncatedSingularValues_tail, truncatedSVD_tail | no | Proven |
| Hagi.External.Flywheel.SpectralNormGap | 30 | 0 | - | no | Proven |
| Hagi.External.Flywheel.TruncatedSVDRank1 | 5 | 4 | - | no | Proven |
| Hagi.External.Flywheel.WeylInequality | 62 | 4 | - | no | Proven |
| Hagi.External.MemT.GDN2 | 27 | 10 | gdn2ApproxIter, gdn2Iter, gdn2Update, rowSumNorm | no | Proven |
| Hagi.Foundations.Chord | 4 | 0 | - | no | Proven |
| Hagi.Foundations.ConeTakeoff | 18 | 0 | - | no | Proven |
| Hagi.Foundations.GrowthBand | 4 | 0 | - | no | Proven |
| Hagi.Foundations.Hoeffding | 30 | 3 | bernRho, bernF, bernDenom | no | Proven |
| Hagi.Foundations.MesoScale | 4 | 0 | - | no | Proven |
| Hagi.Foundations.Ortho | 4 | 0 | - | no | Proven |
| Hagi.Foundations.Potential | 3 | 1 | hagiPotential | no | Proven |
| Hagi.Foundations.QuadEta | 3 | 2 | quadLossAt | no | Proven |
| Hagi.Foundations.Recurrence | 46 | 0 | - | no | Proven |
| Hagi.Foundations.StageCalculus | 10 | 0 | - | yes | Conditional |
| Hagi.Foundations.Telescope | 8 | 0 | - | no | Proven |
| Hagi.Generalization.ModeState | 29 | 33 | computedGenStep, hagiPotential | yes | Empirical |
| Hagi.Geometry.SphericalSimplex | 9 | 0 | - | no | Proven |
| Hagi.Growth.Ceilings | 15 | 1 | - | no | Speculative |
| Hagi.Growth.ChainUnification | 9 | 0 | - | no | Speculative |
| Hagi.Growth.FiberNecessity | 3 | 0 | - | no | Proven |
| Hagi.Growth.GainDecomposition | 25 | 24 | etaState, etaOpt, etaPolicy | no | Speculative |
| Hagi.Growth.GainRenewal | 11 | 1 | gainFromD | yes | Conditional |
| Hagi.Growth.GammaDeficit | 2 | 0 | - | no | Proven |
| Hagi.Growth.Grow | 13 | 1 | certifiedGain | yes | Conditional |
| Hagi.Growth.IntegrationOrder | 3 | 0 | - | no | Proven |
| Hagi.Growth.LinearCone | 97 | 22 | sqrtGain | yes | Speculative |
| Hagi.Growth.NoiseDisentangle | 19 | 1 | avgVec | no | Proven |
| Hagi.Growth.PlasticityLedger | 10 | 3 | famMix, plasticityRadius | no | Proven |
| Hagi.Growth.RecursiveSelfDevelopment | 5 | 1 | realizedSuccess | no | Speculative |
| Hagi.Growth.RoundViability | 3 | 0 | - | no | Speculative |
| Hagi.Growth.RsiCriterion | 9 | 0 | - | no | Speculative |
| Hagi.Growth.Saturation | 5 | 0 | - | no | Speculative |
| Hagi.Growth.SeedOnly | 7 | 0 | - | yes | Speculative |
| Hagi.Growth.SelfDevelopment | 3 | 0 | - | no | Proven |
| Hagi.Growth.StateBinding | 6 | 2 | - | no | Speculative |
| Hagi.Growth.Takeoff | 13 | 1 | - | yes | Speculative |
| Hagi.Growth.Thermostat | 33 | 0 | - | no | Proven |
| Hagi.Information.Capacity | 11 | 3 | repRate | no | Proven |
| Hagi.Learning.BitBudget | 11 | 2 | layerBits, bitsPerTrit | no | Proven |
| Hagi.Learning.ContinualForgetting | 24 | 6 | anchorLedger, adelta, atask, achain | no | Proven |
| Hagi.Learning.FOOF | 3 | 2 | foofW | no | Proven |
| Hagi.Learning.FOOFUnique | 2 | 0 | - | no | Proven |
| Hagi.Learning.HRCN | 3 | 1 | domainTerm | no | Proven |
| Hagi.Learning.HadamardComplete | 2 | 0 | - | no | Proven |
| Hagi.Learning.HadamardParseval | 28 | 0 | - | no | Proven |
| Hagi.Learning.HadamardProjectors | 12 | 4 | charProj, charProjR | no | Proven |
| Hagi.Learning.NetworkBudget | 16 | 0 | - | no | Proven |
| Hagi.Learning.PertTelescope | 5 | 1 | - | no | Proven |
| Hagi.Learning.RCDL | 12 | 4 | expw, weightedSoftmax | no | Proven |
| Hagi.Learning.RegCovPD | 5 | 0 | - | no | Proven |
| Hagi.Learning.RouterMix | 3 | 1 | routerMix | no | Proven |
| Hagi.Learning.SleepingRouter | 45 | 14 | swWeight, sleep_anchor_loss, awPot, swLoss, mixLossOf, swMixLoss, swPredW | no | Proven |
| Hagi.Learning.SoftRouterMix | 13 | 3 | ceDist | no | Proven |
| Hagi.Learning.SoftRouterTotal | 9 | 2 | anchorMix, az | no | Proven |
| Hagi.Learning.SpectralBudget | 3 | 0 | - | no | Proven |
| Hagi.Learning.TernaryPert | 3 | 3 | eunorm, outNorm | no | Proven |
| Hagi.Learning.ToyTrajectory | 21 | 29 | lossS, traj | yes | Conditional |
| Hagi.Learning.TrainingTransition | 14 | 15 | taskQual, taskEnergy | no | Proven |
| Hagi.Legacy | 0 | 0 | - | no | Proven |
| Hagi.Legacy.AdvanceWitness | 3 | 0 | - | yes | Deprecated |
| Hagi.Legacy.ArchitectureTheorem | 79 | 9 | forwardKlTarget, reverseKlTarget, l1Norm, binEnt, distillEfficiency | yes | Deprecated |
| Hagi.Legacy.Assumptions | 29 | 16 | trunc_idle_witness, idleTraj | yes | Deprecated |
| Hagi.Legacy.CertifiedGrowth | 6 | 0 | - | no | Deprecated |
| Hagi.Legacy.CorePremisesDerived | 6 | 0 | - | yes | Deprecated |
| Hagi.Legacy.GrandSynthesis | 6 | 1 | - | no | Deprecated |
| Hagi.Legacy.HAGICertWitness | 6 | 2 | witnessTraj, witnessState | no | Deprecated |
| Hagi.Legacy.LearningKernel | 5 | 3 | - | no | Deprecated |
| Hagi.Legacy.LinkedWitness | 2 | 1 | - | no | Deprecated |
| Hagi.Legacy.MasterChallenge | 1 | 0 | - | no | Deprecated |
| Hagi.Legacy.MasterHAGI | 21 | 5 | - | yes | Deprecated |
| Hagi.Legacy.MasterHAGICoupled | 21 | 11 | coupledGrowthTraj | no | Deprecated |
| Hagi.Legacy.MasterHAGITrunc | 20 | 0 | - | yes | Deprecated |
| Hagi.Legacy.Nonvacuity | 75 | 15 | Spos, Spos', MwEffects, S₀, Mw0, mergeOperationalCertStep, mergeStrictCertStep, S₁, jensenGap, Mw, witnessGap | yes | Deprecated |
| Hagi.Legacy.NonvacuityHorizon | 6 | 2 | satF, satC | no | Deprecated |
| Hagi.Legacy.QuadraticConcrete | 17 | 4 | quadGen, quadE, quadGen', quadState | no | Deprecated |
| Hagi.Legacy.RecursiveGrowth | 24 | 0 | - | yes | Deprecated |
| Hagi.Legacy.StateTakeoff | 4 | 0 | - | yes | Deprecated |
| Hagi.Legacy.TernaryGrad | 6 | 0 | - | no | Deprecated |
| Hagi.Legacy.TopLevel | 15 | 0 | - | yes | Deprecated |
| Hagi.Math.Info.InfoCore | 145 | 24 | ceDef, softDef, logDetShift, entropy, spectralFactor, entDef, klDef, tvDef, logEntropyPrimitive, shannon, tvHalf, logGram | no | Proven |
| Hagi.Model.Adaptive | 20 | 1 | - | no | Proven |
| Hagi.Model.AdaptiveChunking | 50 | 12 | floorCappedChunks, adaptiveCost, floorBoundaryChunks | no | Proven |
| Hagi.Model.AlignmentRisk | 3 | 0 | - | no | Proven |
| Hagi.Model.Attention | 48 | 17 | stdIO, ropeInner, rot, flashIO, cacheFull, cacheLatent | no | Proven |
| Hagi.Model.AttentionSpend | 25 | 4 | - | no | Proven |
| Hagi.Model.AttentionTransfer | 11 | 19 | attnStack, attnGain, attnBlockBranch, attnBranch, attnBlockList | no | Proven |
| Hagi.Model.BYOL | 11 | 5 | cosS, qnorm, bl, dsum | no | Proven |
| Hagi.Model.BackboneTransfer | 18 | 2 | - | no | Proven |
| Hagi.Model.BatchCEDescent | 0 | 0 | - | no | Proven |
| Hagi.Model.BatchCEDescentArithmetic | 49 | 11 | batchLoss, batchGradientMinimizer, batchResidualGradient, batchCommonSafeEta, batchAlignment, batchRangeSquare, batchMeanDirection, batchCommonNextParameters, meanResidualTranspose, batchMeanAction, batchCommonSafeWindow | no | Proven |
| Hagi.Model.BatchCEDescentCommon | 18 | 5 | dirRange, dirAction, batchFeatureRangeCoefficient, dirMajorizer, alongNext | no | Proven |
| Hagi.Model.BatchCEDescentDirection | 48 | 5 | batchDirectionNextParameters, batchDirectionSafeWindow, batchDirectionQuadraticMargin, batchDirectionSafeEta, batchDirectionMargin | no | Proven |
| Hagi.Model.BatchCEDescentFixtures | 26 | 3 | - | no | Proven |
| Hagi.Model.BatchCEDescentHalfEta | 35 | 4 | batchDirectionHalfMargin, batchDirectionMinQuadraticMargin, batchDirectionHalfNextParameters, batchDirectionHalfEta | no | Proven |
| Hagi.Model.BatchCEDescentLogitRange | 26 | 5 | dirLogitRange, batchLogitSafeStep, batchLogitMajorizer, batchLogitRangeSquare, batchLogitNextParameters | no | Proven |
| Hagi.Model.BatchCEDescentResidualNorm | 20 | 1 | featureNormSum | no | Proven |
| Hagi.Model.BatchCEDescentSafeStep | 32 | 3 | batchNextParameters, batchMajorizer, batchSafeStep | no | Proven |
| Hagi.Model.BatchCEDescentStochastic | 18 | 1 | stochasticStepDraw | yes | Conditional |
| Hagi.Model.BlockNorm | 17 | 5 | globalRms, globalNorm, blockNorm, blockRms | no | Proven |
| Hagi.Model.CEConfidenceScale | 19 | 0 | - | no | Proven |
| Hagi.Model.CECoupledShortcut | 18 | 2 | shortcutScales, packedShortcutScales | no | Proven |
| Hagi.Model.CEDescent | 63 | 13 | ceAlignment, ceMajorizer, ceRangeMajorizer, ceStepLogitRange, ceLogits, ceDirection, ceRangeSafeStep, ceResidual, safeStepSize, ceNextLogits, ceNextParameters, residualTranspose, ceStepRange | no | Proven |
| Hagi.Model.CEExpansion | 10 | 4 | expandedReadoutJacobian, expandedParameters | no | Proven |
| Hagi.Model.CEGlobalConvergence | 86 | 5 | ceGrad, plStep, ceGradReg, ceReg | no | Proven |
| Hagi.Model.CEGradient | 25 | 3 | featureCLM, lseDeriv | no | Proven |
| Hagi.Model.CEGroupedScale | 66 | 15 | blockPenalty, packedBlocks, groupStructuralPenalty, groupObservedPenalty, selectedGroupScalesExec, blockParameters, blockWeights, quantizedBlock, selectedGroupScales, jointParameters | no | Proven |
| Hagi.Model.CEGroupedScaleBasic | 0 | 1 | featureAbsSum | no | Proven |
| Hagi.Model.CEHeldout | 35 | 6 | decodeJoint, encodeJoint, normalizedCE, ceBound, unionConfFactor | no | Proven |
| Hagi.Model.CEJacobianMajorizer | 1 | 0 | - | no | Proven |
| Hagi.Model.CEJointScale | 34 | 4 | selectedCoupledScales, jointObservedPenalty, packedCoupledScales, coupledPenalty | no | Proven |
| Hagi.Model.CEMarkovConfidence | 5 | 0 | - | no | Proven |
| Hagi.Model.CEMarkovMaximalConfidence | 2 | 1 | - | no | Proven |
| Hagi.Model.CEMarkovSelectedPrefix | 1 | 0 | - | no | Proven |
| Hagi.Model.CEPackedStep | 7 | 4 | packedStep, decodeStep, rawSuccessor, encodedWord | no | Proven |
| Hagi.Model.CEPadding | 67 | 10 | - | no | Proven |
| Hagi.Model.CEQuantized | 20 | 5 | ceQuantPenalty, ceQuantObservedPenalty, ternaryCEParameters, ceQuantStructuralPenalty | no | Proven |
| Hagi.Model.CEScaleSelection | 17 | 4 | selectedScale, scalePenalty, packedSelected | no | Proven |
| Hagi.Model.CEStorageBound | 4 | 0 | - | no | Proven |
| Hagi.Model.CertifiedTransition | 36 | 10 | toCertStepGen | yes | Conditional |
| Hagi.Model.ComputeOptimal | 8 | 1 | chinchillaLoss | no | Proven |
| Hagi.Model.ConsolidationMirror | 6 | 0 | - | no | Proven |
| Hagi.Model.CycleCertificate | 23 | 14 | growSeq_cycle_certificate | no | Proven |
| Hagi.Model.DiffAttention | 5 | 2 | sm, diffW | no | Proven |
| Hagi.Model.DistillCert | 13 | 16 | quantStudent | no | Proven |
| Hagi.Model.EnergyReasoning.AlternatingRound | 16 | 2 | yan2, fan2 | no | Proven |
| Hagi.Model.EnergyReasoning.AttentionCoupling | 14 | 6 | attentionCoupling, κa3, wa3, attentionK, attentionWeights | no | Proven |
| Hagi.Model.EnergyReasoning.CramContracts | 75 | 83 | toCertStepGen, toKernelCertStep, toLossCeilingDrop | no | Proven |
| Hagi.Model.EnergyReasoning.EnergyClassGeneralization | 5 | 0 | - | no | Proven |
| Hagi.Model.EnergyReasoning.EnergySearch | 24 | 7 | heatbathWeight, heatbathKernel, focusedMixture, boltzmannDensity | no | Proven |
| Hagi.Model.EnergyReasoning.EnergyStopping | 12 | 21 | - | no | Proven |
| Hagi.Model.EnergyReasoning.GreedyTermination | 7 | 1 | focusedDisagreementWeight | no | Proven |
| Hagi.Model.EnergyReasoning.HeatBathMixing | 29 | 7 | vecMul, hbChain, stationaryDensity | no | Proven |
| Hagi.Model.EnergyReasoning.LatentEnergy | 39 | 8 | zstar4, latentGradient, latentEnergy, latentQuadraticForm, latentUpdate, visibleBiasWithZ | no | Proven |
| Hagi.Model.EnergyReasoning.LatentSupport | 24 | 5 | zstar2 | no | Proven |
| Hagi.Model.EnergyReasoning.NumericalRobustness | 7 | 0 | - | no | Proven |
| Hagi.Model.EnergyReasoning.Pseudolikelihood | 2 | 3 | conditionalDist, pseudolikelihoodObjective, conditionalLogit | no | Proven |
| Hagi.Model.EnergyReasoning.PseudolikelihoodLocalField | 24 | 15 | freeCellPseudolikelihood, localFieldLogit, symmetrizeCoupling | no | Proven |
| Hagi.Model.EnergyReasoning.SparseField | 16 | 8 | sparseLocalField, Kex4 | no | Proven |
| Hagi.Model.EnergyReasoning.ValiditySeparation | 15 | 5 | - | no | Proven |
| Hagi.Model.FastArch3Transfer | 16 | 30 | fa3HeadLoss, fa3Objective, fa3BlockList, fa3Gain, fa3Stack | no | Proven |
| Hagi.Model.GDNBridge | 13 | 4 | gdnUpdate | no | Proven |
| Hagi.Model.GDNTransfer | 24 | 35 | gdnBlockBranch, gdnGain, hybStack, hybBlockList, gdnMix, gdnBlockList, hybGain, gdnGateTanh, gdnStack | yes | Conditional |
| Hagi.Model.GatedCEDescent | 11 | 5 | gatedAlignment, gatedLineObjective, gatedDirection, gatedResidualTranspose, gatedNextParameters | no | Proven |
| Hagi.Model.GatedCEGradient | 23 | 4 | gatedProjection, gatedJacobian, gatedForward, gatedAction | no | Proven |
| Hagi.Model.GatedCEPositiveCurvature | 3 | 0 | - | no | Proven |
| Hagi.Model.GatedCESafeStep | 52 | 11 | gatedSafeDrop, gatedStepRange, gatedCurvature, gatedDisplacement, gatedResidual, gatedMajorizer, gatedLogitRemainder, gatedUnitAbsLogit, gatedSafeStepSize, gatedResidualSecondOrderMass, gatedUnitSecondOrderMass | no | Proven |
| Hagi.Model.GatedCEUniformCurvature | 17 | 4 | gatedColumnAbsSum, gatedSecondOrderFeatureMass, gatedCurvatureUniformBound, gatedFirstOrderFeatureMass | no | Proven |
| Hagi.Model.Generative | 11 | 2 | alphaBar, flowPath | no | Proven |
| Hagi.Model.Grokfast | 4 | 3 | gLow, ampDir, gHigh | no | Proven |
| Hagi.Model.HNet | 19 | 1 | hnetOptRatio | no | Proven |
| Hagi.Model.HNet2 | 11 | 3 | hier2Cost, denseCost, hier2Positions | no | Proven |
| Hagi.Model.HypothesisCompetition | 29 | 8 | dhcStep, dhcTotal, dhcOrbit, dhcWeights | no | Proven |
| Hagi.Model.LabelSmoothing | 5 | 2 | lsH, lsTarget | no | Proven |
| Hagi.Model.LayerNorm | 13 | 3 | variance, mean, lnVec | no | Proven |
| Hagi.Model.Logic.VennHead | 27 | 11 | vennHead, vAtoms, relu, vAtom, venn2Head | no | Proven |
| Hagi.Model.LogitPSV | 4 | 2 | - | no | Proven |
| Hagi.Model.Losses | 29 | 6 | gnWeight, tanhE, tl, softcap, vh, nt2 | no | Proven |
| Hagi.Model.MachineBridge | 12 | 2 | machineStageInputN, machineStageInput | no | Proven |
| Hagi.Model.MambaSSM | 11 | 0 | - | no | Proven |
| Hagi.Model.MeasuredEffects | 24 | 66 | - | no | Proven |
| Hagi.Model.MeasurementCert | 11 | 13 | - | no | Proven |
| Hagi.Model.Memory | 7 | 4 | wtParams, untiedParams | no | Proven |
| Hagi.Model.Mixup | 2 | 2 | mixLabel, mixScore | no | Proven |
| Hagi.Model.ModeConnectivity | 11 | 0 | - | no | Proven |
| Hagi.Model.ModelSoup | 6 | 6 | ema | no | Proven |
| Hagi.Model.ModernHopfield | 5 | 0 | - | no | Proven |
| Hagi.Model.MuPScaling | 5 | 2 | muPUpdate | no | Proven |
| Hagi.Model.NeuralComputer | 13 | 33 | - | no | Proven |
| Hagi.Model.NormAct | 8 | 5 | swiglu, attP, sig, swish | no | Proven |
| Hagi.Model.Perceiver | 13 | 4 | - | no | Proven |
| Hagi.Model.QuantizedAdvance | 5 | 1 | - | no | Proven |
| Hagi.Model.RL | 15 | 3 | groupAdv, dpoReward, btPref | no | Proven |
| Hagi.Model.RMSNorm | 14 | 2 | ms, rnVec | no | Proven |
| Hagi.Model.RMSNormTransfer | 53 | 4 | μnEps, rnEpsEuc, rnEuc, msE | no | Proven |
| Hagi.Model.RVCore | 14 | 5 | - | no | Proven |
| Hagi.Model.RamProtocol | 32 | 25 | - | no | Proven |
| Hagi.Model.ReferenceMachine | 63 | 12 | machineStep, energyE, quantErr, quantErrNorm, energy, compressQE, compressQ, machineGap | no | Proven |
| Hagi.Model.Residual | 4 | 10 | - | no | Proven |
| Hagi.Model.ResidualVQ | 74 | 6 | latQ, refineStageEffects, reconstruct | no | Proven |
| Hagi.Model.RoPETransfer | 17 | 6 | attnRopeStack, attnRopeGain, rotEuc, attnRopeBlockList | no | Proven |
| Hagi.Model.Routing | 10 | 3 | dwScores, vstep, adv | no | Proven |
| Hagi.Model.Sidon | 6 | 1 | - | no | Proven |
| Hagi.Model.SoftmaxHead | 41 | 45 | apply, headCE, headLoss | no | Proven |
| Hagi.Model.SoftmaxStep | 26 | 2 | logitGrad, logitCE | yes | Conditional |
| Hagi.Model.SourceMixture | 4 | 3 | successDist | no | Proven |
| Hagi.Model.SpecDecoding | 20 | 6 | anchorSeq | no | Proven |
| Hagi.Model.StageSemantics | 131 | 42 | wS0, wU2, growInput, growSeq, wTraj, growTraj, wU1, wTraj2, wU0 | no | Proven |
| Hagi.Model.TanhCEStep | 25 | 3 | tanhJacobian, tanhEmbedding, tanhModel | no | Proven |
| Hagi.Model.TanhTaylor | 5 | 1 | sechSq | no | Proven |
| Hagi.Numerics.SoftmaxFix | 30 | 2 | expTilt, logitMargin | no | Proven |
| Hagi.Optimization.AdaGrad | 3 | 1 | adagradAcc | no | Proven |
| Hagi.Optimization.AdamBias | 19 | 1 | - | no | Proven |
| Hagi.Optimization.AdamW | 2 | 2 | l2Step | no | Proven |
| Hagi.Optimization.AdaptiveCycle | 2 | 0 | - | no | Proven |
| Hagi.Optimization.CautiousOptimizer | 4 | 1 | cautiousMask | no | Proven |
| Hagi.Optimization.Checkpoint | 2 | 0 | - | no | Proven |
| Hagi.Optimization.ComputeScaling | 11 | 0 | - | no | Proven |
| Hagi.Optimization.DREAM | 10 | 20 | - | no | Proven |
| Hagi.Optimization.DirectionPacking | 13 | 1 | Sop | no | Proven |
| Hagi.Optimization.EF21Markov | 6 | 1 | - | no | Proven |
| Hagi.Optimization.EF21Quantizer | 14 | 3 | qTernVec | no | Proven |
| Hagi.Optimization.GradAccum | 1 | 2 | fullGrad, microGrad | no | Proven |
| Hagi.Optimization.GraphDistanceRouting | 52 | 7 | targetRank, shortestToTargetKernel, partialShortestToTargetRows, shorterNeighborFinset | no | Proven |
| Hagi.Optimization.HBRate | 39 | 2 | - | no | Proven |
| Hagi.Optimization.InexactContraction | 5 | 0 | - | no | Proven |
| Hagi.Optimization.InfoPreservation | 0 | 0 | - | no | Proven |
| Hagi.Optimization.LLRD | 4 | 1 | - | no | Proven |
| Hagi.Optimization.LRSchedule | 9 | 2 | cosLR | no | Proven |
| Hagi.Optimization.Lion | 2 | 2 | signStep, sgn | no | Proven |
| Hagi.Optimization.Lookahead | 3 | 1 | - | no | Proven |
| Hagi.Optimization.MirrorHedge | 0 | 0 | - | no | Proven |
| Hagi.Optimization.MirrorHedgeCore | 25 | 1 | mirrorStep | no | Proven |
| Hagi.Optimization.MirrorHedgeEnergy | 10 | 1 | stepNorm | no | Proven |
| Hagi.Optimization.MirrorHedgeRegret | 30 | 5 | mirrorIterate | no | Proven |
| Hagi.Optimization.MirrorHedgeRouting | 4 | 0 | - | no | Proven |
| Hagi.Optimization.MirrorHedgeSurvivor | 27 | 7 | ewNorm, ewPot, ewWeight | no | Proven |
| Hagi.Optimization.MirrorHedgeWealth | 9 | 0 | - | no | Proven |
| Hagi.Optimization.Momentum | 50 | 1 | momentumRate | no | Proven |
| Hagi.Optimization.MomentumHB | 8 | 3 | hbErr | no | Proven |
| Hagi.Optimization.NeuronAlloc | 3 | 0 | - | no | Proven |
| Hagi.Optimization.PLConvergence | 9 | 0 | - | no | Proven |
| Hagi.Optimization.PPOClip | 6 | 1 | - | no | Proven |
| Hagi.Optimization.PolyStep | 4 | 3 | polyStepUpdate, polyWeights, polyDelta | no | Proven |
| Hagi.Optimization.RobbinsMonro | 3 | 0 | - | no | Proven |
| Hagi.Optimization.SAM | 5 | 3 | samW, norm2 | no | Proven |
| Hagi.Optimization.SphericalDamping | 7 | 0 | - | no | Proven |
| Hagi.Optimization.SubspaceGrowth | 6 | 1 | projResidual | no | Proven |
| Hagi.Planning.Imagination | 6 | 0 | - | yes | Conditional |
| Hagi.Pretraining.DataPruning | 3 | 0 | - | no | Proven |
| Hagi.Pretraining.Dust | 19 | 6 | esEst, hcAvg | no | Proven |
| Hagi.Pretraining.DustAlign | 62 | 3 | pairQ, Nrm, prodQ | no | Proven |
| Hagi.Pretraining.DustMeasure | 12 | 3 | rademacherLaw, fairBoolMeasure | no | Proven |
| Hagi.Pretraining.Grokking | 13 | 0 | - | no | Proven |
| Hagi.Pretraining.ProbeError | 104 | 14 | boundedProbeOptimalStep, probeGridRound, noisyCentralCubicProbe, gridCentralCubicProbe, centralCubicProbe, probeCubicEnergy, mlpResidual, probeQuadraticEnergy, probeOptimalStep, probeCost, forwardQuadraticProbe, probeCubicGrad, centralQuadraticProbe | yes | Conditional |
| Hagi.Pretraining.RobustnessLaw | 8 | 0 | - | no | Proven |
| Hagi.Pretraining.Speedrun | 15 | 1 | ceLogit | no | Proven |
| Hagi.Pretraining.SyntheticPretrain | 3 | 2 | synthGain, TimeToCapability | yes | Empirical |
| Hagi.Pretraining.TrustRegion | 3 | 0 | - | no | Proven |
| Hagi.Probability.AdaptiveSuccess | 2 | 1 | - | no | Proven |
| Hagi.Probability.Azuma | 17 | 7 | - | no | Proven |
| Hagi.Probability.BatchSNR | 18 | 5 | snr, stepCost, gainPerCost, criticalBatch, batchGain | no | Proven |
| Hagi.Probability.BernoulliFactory | 3 | 4 | - | no | Proven |
| Hagi.Probability.CertifiedEstimator | 38 | 6 | - | no | Proven |
| Hagi.Probability.ChernoffCGF | 26 | 0 | - | no | Proven |
| Hagi.Probability.Concentration | 25 | 3 | concConfidenceTwoSided, concConfidence, concRadius | no | Proven |
| Hagi.Probability.ConditionalSuccess | 17 | 1 | concDelta | yes | Empirical |
| Hagi.Probability.EntropyConvexity | 34 | 0 | - | no | Proven |
| Hagi.Probability.ExpChord | 18 | 0 | - | no | Proven |
| Hagi.Probability.FannesPinsker | 83 | 1 | dirac | no | Proven |
| Hagi.Probability.FiniteBayes | 14 | 4 | mode, observationEvidence, posterior, zeroOneLoss | no | Proven |
| Hagi.Probability.FiniteEM | 29 | 2 | jointMass, mStep | no | Proven |
| Hagi.Probability.FiniteFamilyConfidence | 48 | 5 | instDecidablePredForallFinOfNatNatTwoModelGood, populationMean, twoModelP, twoModelGood | no | Proven |
| Hagi.Probability.FiniteFamilyConfidenceEmpirical | 0 | 1 | empiricalMean | no | Proven |
| Hagi.Probability.FiniteHamming | 11 | 4 | coordinateDecoder, coordinateMode, hammingRisk, coordinateLaw | no | Proven |
| Hagi.Probability.FiniteJointLogScore | 23 | 2 | conditionalRow | no | Proven |
| Hagi.Probability.FiniteLogScore | 18 | 0 | - | no | Proven |
| Hagi.Probability.FiniteMultiEM | 7 | 1 | batchMStep | no | Proven |
| Hagi.Probability.Freedman | 9 | 3 | - | yes | Empirical |
| Hagi.Probability.FreedmanFamilyConfidence | 6 | 1 | - | no | Proven |
| Hagi.Probability.FreedmanStep | 27 | 15 | stochastic_safe_step_closed, stochastic_safe_step, driftAdditive, stochastic_safe_step_variance | yes | Conditional |
| Hagi.Probability.FreedmanTwoSided | 101 | 17 | historyInitial, historyAdditive, historyIncrement, historyNoise, historyLaw, historyKernel, markovLaw, historyCounter, pmfMean, historyCounterRate, uniformOfFinset | no | Proven |
| Hagi.Probability.GibbsCooling | 46 | 0 | - | no | Proven |
| Hagi.Probability.GibbsCore | 96 | 3 | tilted, gibbsW, gibbsZ | no | Proven |
| Hagi.Probability.KLSBridge | 14 | 4 | - | no | Proven |
| Hagi.Probability.LinkedFlip | 41 | 18 | eventMask, support, uniformPlane, linkedChannel, linkedMask, changedCount | no | Proven |
| Hagi.Probability.MarkovPathSupport | 11 | 1 | - | no | Proven |
| Hagi.Probability.MirrorHedgeCertificates | 11 | 0 | - | no | Proven |
| Hagi.Probability.MirrorHedgeGibbs | 6 | 0 | - | no | Proven |
| Hagi.Probability.MirrorHedgeMWU | 24 | 0 | - | no | Proven |
| Hagi.Probability.MirrorHedgeMWUSelectedGradient | 20 | 2 | selectedMeanGradientMSE, selectedGradientMSE | no | Proven |
| Hagi.Probability.MirrorHedgeMWUSelectedLoss | 29 | 2 | selectedLoss_optimalPropensity, selectedLossMSE | no | Proven |
| Hagi.Probability.MomentBounds | 16 | 0 | - | no | Proven |
| Hagi.Probability.NoiseTemperature | 61 | 5 | popVar, popMean, batchMean, uniP, centered | no | Proven |
| Hagi.Probability.PMFBridge | 7 | 2 | - | no | Proven |
| Hagi.Probability.RankedStopRouting | 33 | 17 | classifyRouting | no | Proven |
| Hagi.Probability.SphericalAngle | 57 | 1 | sphericalAngle | no | Proven |
| Hagi.Probability.StationaryFlatness | 10 | 2 | expectNat, probGe | no | Proven |
| Hagi.Probability.ThermoAxes | 2 | 0 | - | no | Proven |
| Hagi.Probability.ThermoBridge | 2 | 0 | - | no | Proven |
| Hagi.Probability.WSqD | 10 | 0 | - | no | Proven |
| Hagi.Research | 0 | 0 | - | no | Proven |
| Hagi.Research.ConditionalInformation | 33 | 4 | conditionalMutualInformation | no | Speculative |
| Hagi.Research.CrossModalGap | 10 | 3 | crossModalGap | no | Speculative |
| Hagi.Research.MarkovPercolation | 22 | 7 | weightedNeighborKernel, maskedNeighborWeights, neighborOrStayKernel, uniformNeighborKernel | no | Speculative |
| Hagi.Research.OmniInvariant | 10 | 2 | - | no | Speculative |
| Hagi.Research.OmniState | 12 | 2 | - | no | Speculative |
| Hagi.Research.PPT | 41 | 16 | goodSet, pptTarget, pptSwapKernel, pptNorm, pptSwapAccept | yes | Speculative |
| Hagi.Research.PPTCanonical | 2 | 0 | - | no | Speculative |
| Hagi.Research.Schelling | 12 | 3 | localCompatibleDegree, locallySatisfied | no | Speculative |
| Hagi.Research.SchellingCandidateSelection | 1 | 2 | - | no | Speculative |
| Hagi.Research.SchellingMarkovRouting | 2 | 0 | - | no | Speculative |
| Hagi.Research.SchellingPercolation | 11 | 0 | - | no | Speculative |
| Hagi.Research.Site | 29 | 22 | percolationSystem, R | no | Speculative |
| Hagi.Runtime.BF16Delta | 74 | 30 | - | no | Proven |
| Hagi.Runtime.ControllerGates | 38 | 1 | - | no | Proven |
| Hagi.Runtime.DyadicTernary | 38 | 8 | dyadicLevel | no | Proven |
| Hagi.Runtime.LiveDeltaQuant | 2 | 1 | quantMat | no | Proven |
| Hagi.Runtime.TernaryCodec | 9 | 5 | ternaryValueEncode, packedTernarySamples, ternaryValueDecode | no | Proven |
| Hagi.Runtime.TernaryExact | 13 | 3 | satTail, qTern | yes | Conditional |
| Hagi.Runtime.VennPacking | 15 | 4 | vennTritRow, rowByte, rowWord | no | Proven |
| Hagi.Sparsity.SparseStep0 | 1 | 0 | - | no | Proven |
| Hagi.Spectral.RankGrowth | 2 | 2 | - | no | Proven |
| Hagi.StatMech.Hopfield.CharPatterns | 12 | 3 | sylvesterRR, charEnergy | no | Proven |
| Hagi.StatMech.Hopfield.Concentration | 12 | 0 | - | no | Proven |
| Hagi.StatMech.Hopfield.LowerBound | 4 | 0 | - | no | Proven |
| Hagi.StatMech.Hopfield.Model | 3 | 5 | partition, freeEnergyDensity, energy | no | Proven |
| Hagi.StatMech.Hopfield.SubMemory | 12 | 1 | subsetEnergy | no | Proven |
| Hagi.State.TrainState | 19 | 90 | qualityScalar | no | Proven |
| Hagi.State.Transition | 27 | 36 | lossOf, trainStep, guidedTrainStep | no | Proven |
| Hagi.State.Views | 3 | 1 | - | no | Proven |
| Hagi.Step.AdaptiveSafeQP | 17 | 4 | adaptiveNoiseEps, latticeStep, latticeNet | yes | Empirical |
| Hagi.Step.ArmijoAcceptance | 9 | 0 | - | no | Proven |
| Hagi.Step.BatchBudget | 10 | 0 | - | no | Proven |
| Hagi.Step.CPUFreeze | 4 | 1 | - | no | Proven |
| Hagi.Step.CausalFilter | 28 | 17 | - | no | Proven |
| Hagi.Step.Compound | 6 | 0 | - | yes | Empirical |
| Hagi.Step.Dominate | 6 | 0 | - | no | Proven |
| Hagi.Step.FrobeniusLMO | 13 | 0 | - | no | Proven |
| Hagi.Step.GPM | 5 | 3 | - | no | Proven |
| Hagi.Step.GradCentralization | 4 | 1 | gc | no | Proven |
| Hagi.Step.GradClip | 5 | 1 | clip | no | Proven |
| Hagi.Step.HybridState | 3 | 0 | - | no | Proven |
| Hagi.Step.Joint | 4 | 1 | quadIncr | no | Proven |
| Hagi.Step.JointPreserve | 6 | 0 | - | no | Proven |
| Hagi.Step.LazyAdam | 7 | 0 | - | no | Proven |
| Hagi.Step.LiveDeltaSafe | 6 | 2 | - | no | Proven |
| Hagi.Step.MDLObjective | 5 | 1 | - | no | Proven |
| Hagi.Step.MDLThreeCurrency | 5 | 4 | dataCodeLen, sourceEntropy | no | Proven |
| Hagi.Step.Muon | 30 | 3 | ns | no | Proven |
| Hagi.Step.NCEExact | 25 | 5 | impW, secondMomentW, qMean, secondMoment, partZ | no | Proven |
| Hagi.Step.NewtonPolar | 27 | 4 | newtonIter, newtonStep, nsStep, nsIter | no | Proven |
| Hagi.Step.NewtonSchulzMatrix | 9 | 1 | nsMatrixStep | no | Proven |
| Hagi.Step.NewtonSchulzSpectral | 4 | 0 | - | no | Proven |
| Hagi.Step.NoisyPL | 17 | 0 | - | no | Proven |
| Hagi.Step.PreconditionerDescent | 9 | 0 | - | no | Proven |
| Hagi.Step.ProjectionDescent | 26 | 2 | segmentMinNormCoefficient, segmentMinNorm | yes | Conditional |
| Hagi.Step.RiemannNewtonPolar | 8 | 0 | - | no | Proven |
| Hagi.Step.RobustDescent | 3 | 0 | - | no | Proven |
| Hagi.Step.SNRWeights | 9 | 0 | - | no | Proven |
| Hagi.Step.SafeQP | 22 | 6 | - | no | Proven |
| Hagi.Step.SafeQPStep | 36 | 3 | safeqpEtaMax, safeqpEtaMaxConflictFree | yes | Conditional |
| Hagi.Step.SignSGD | 5 | 1 | sgn1 | no | Proven |
| Hagi.Step.StochasticSafeQP | 38 | 1 | noiseEps | yes | Empirical |
| Hagi.Step.SubspaceSafeQP | 1 | 0 | - | no | Proven |
| Hagi.Step.Upgrades | 19 | 3 | nce_per_sample_corrected, softmaxW | no | Proven |
| Hagi.Step.VariantSafeQP | 10 | 3 | transportedGrad | no | Proven |
| Hagi.Step.WarmupSchedule | 5 | 1 | warmupEta | no | Proven |
| Hagi.Step.WeightDecay | 8 | 0 | - | no | Proven |
| Hagi.System.Certificates | 39 | 82 | - | no | Proven |
| Hagi.System.DiscreteStep | 1 | 0 | - | no | Proven |
| Hagi.System.GrowthComputed | 5 | 2 | growthQuad | no | Proven |
| Hagi.System.GrowthState | 43 | 127 | stageCertificate, gainJoint, verify, costCompress | yes | Conditional |
| Hagi.System.GrowthStateViews | 17 | 63 | - | no | Proven |
| Hagi.System.StepCertificate | 12 | 17 | bestFeasibleDecrease, toCertStepGen, stepCertificateOfParts, instDecidablePredStepCertificateStepFeasible | no | Proven |
| Hagi.System.UnifiedStep | 2 | 0 | - | no | Proven |
| Hagi.Unified.AnytimeMartingale | 32 | 0 | - | yes | Empirical |
| Hagi.Unified.AnytimePACBayes | 2 | 0 | - | no | Proven |
| Hagi.Unified.CanonicalParams | 4 | 4 | canonWeights | no | Proven |
| Hagi.Unified.CapabilityLocal | 2 | 0 | - | no | Proven |
| Hagi.Unified.CertifiedLoop | 27 | 17 | - | no | Proven |
| Hagi.Unified.CertifiedLoopKernel | 46 | 18 | anchorB, anchorObj, anchorW, anchorKm, anchorStep1, anchorStep0, anchorChain, anchorObl | no | Proven |
| Hagi.Unified.CertifiedTrajectory | 2 | 0 | - | no | Proven |
| Hagi.Unified.CommitGate | 16 | 20 | gateDecision, toCertStepGen, instDecidableGate | no | Proven |
| Hagi.Unified.CostComposition | 13 | 2 | - | no | Proven |
| Hagi.Unified.CountableStitching | 10 | 1 | stitchedMasterCountable | no | Proven |
| Hagi.Unified.Ctv2Telescope | 22 | 7 | protoMeasured, stepDrop, scOf, ecToSc, ctv2Honest, smToExec | yes | Conditional |
| Hagi.Unified.DerivAlong | 17 | 0 | - | yes | Conditional |
| Hagi.Unified.DescentCore | 6 | 15 | nrm2, inprod | no | Proven |
| Hagi.Unified.DescentCoreDiag | 14 | 4 | diagE, diagObjective | no | Proven |
| Hagi.Unified.DescentCoreQuad | 11 | 3 | quadE, quadObjective | no | Proven |
| Hagi.Unified.Distillation | 13 | 2 | binEntropy, softProb | no | Proven |
| Hagi.Unified.EFTheory | 37 | 3 | thrComp, signComp | no | Proven |
| Hagi.Unified.EmpiricalPremises | 7 | 16 | - | no | Proven |
| Hagi.Unified.ExecutableController | 24 | 37 | - | no | Proven |
| Hagi.Unified.ExecutableSelection | 17 | 10 | - | no | Proven |
| Hagi.Unified.ExecutedCert | 16 | 13 | toCertStep, toCertStepGen | no | Proven |
| Hagi.Unified.FunctionalState | 6 | 16 | fsCapa, fsEnergy, funStep, funStepJoint | no | Proven |
| Hagi.Unified.GaugeQuotient | 20 | 17 | quotientResidual, seq, rot | no | Proven |
| Hagi.Unified.GrowthComputedCert | 3 | 2 | next, stepCert | no | Proven |
| Hagi.Unified.GuardedRobustLogit | 11 | 1 | guardedLogitNext | no | Proven |
| Hagi.Unified.GuardedRobustResourceMin | 7 | 1 | guardedMinimumResource | no | Proven |
| Hagi.Unified.GuardedRobustSelection | 4 | 2 | guardedRobustNext | no | Proven |
| Hagi.Unified.GuardedRobustTrajectory | 94 | 14 | fixedBiasBinaryPath, scaledBiasBinaryValueEstimate, scaledBiasBinaryPath, scaledBiasBinaryProgressCount, inverseScaledController, fixedBiasBinaryValueEstimate, fixedBiasBinaryGain, guardedRobustPath, guardedRobustGain, scaledBiasBinaryGain, fixedBiasBinaryProgressCount | no | Proven |
| Hagi.Unified.HonestTransition | 23 | 24 | quadObj | no | Proven |
| Hagi.Unified.InterpretiveGrowth | 8 | 5 | passiveMass, pointEffect, liveMass, causalEffect | no | Proven |
| Hagi.Unified.LinkedProjects | 1 | 0 | - | no | Proven |
| Hagi.Unified.LinkedQVec | 10 | 26 | qgen | no | Proven |
| Hagi.Unified.LiveDeltaCycle | 10 | 25 | - | no | Proven |
| Hagi.Unified.Liveness | 3 | 0 | - | no | Proven |
| Hagi.Unified.LogitCert | 12 | 6 | logitStepCert', logitStepCert, logitStepCertExact', logitStepCertExactCore, logitMeasured, logitStepCertExact | yes | Conditional |
| Hagi.Unified.LogitGrowth | 45 | 12 | step, trajectory, orbit, initial, next, unitEta, measuredInput | no | Proven |
| Hagi.Unified.LoopInstances | 11 | 7 | quadStepCert, quadFloor, quadMeasured, quadCert | no | Proven |
| Hagi.Unified.MachineProto | 26 | 21 | fsTraj, fsGate, evalCapa, machineProto | no | Proven |
| Hagi.Unified.MemoryCycle | 43 | 36 | frobNorm | no | Proven |
| Hagi.Unified.MemorySemantics | 15 | 21 | ramWriteCert_of_updateRow | no | Proven |
| Hagi.Unified.MicroStepCert | 4 | 2 | - | no | Proven |
| Hagi.Unified.ModelComparison | 18 | 16 | zIndicator, zOf, Score, modelGap | no | Proven |
| Hagi.Unified.NCStepCert | 20 | 6 | ncContract, ncTraj, ncStepCert, ncMinimalStepCert, ncCertStep, ncMeasured | no | Proven |
| Hagi.Unified.NegativeTests | 6 | 0 | - | no | Proven |
| Hagi.Unified.OptimalConfig | 16 | 20 | - | no | Proven |
| Hagi.Unified.ParetoExecution | 38 | 25 | robustNext, selection, selectedNext, selectionIn, scoreDominatingIn | no | Proven |
| Hagi.Unified.ParetoLogit | 38 | 7 | logitEstimate, logitProblem, logitTrajCert, logitProblemSafeDecidable, logitStepFun, logitSafeDecidable | no | Proven |
| Hagi.Unified.ProductiveTransition | 3 | 1 | - | yes | Conditional |
| Hagi.Unified.QuadMachine | 22 | 10 | machineCert, commitInd, commitCount, gateTraj, quantLift, gateStep | no | Proven |
| Hagi.Unified.QualityResourceMin | 6 | 3 | minimumResource | no | Proven |
| Hagi.Unified.QuantSafeUpdate | 9 | 0 | - | no | Proven |
| Hagi.Unified.RateTheory | 27 | 7 | - | no | Proven |
| Hagi.Unified.RecursiveClean | 19 | 21 | timeConsistency, piR, indepMass, branchLocality | no | Proven |
| Hagi.Unified.RobustCostSensitivity | 3 | 0 | - | no | Proven |
| Hagi.Unified.RobustRadius | 4 | 1 | estimatedMaxValue | no | Proven |
| Hagi.Unified.RobustResourceMin | 8 | 1 | robustMinimumResource | no | Proven |
| Hagi.Unified.SignComp | 22 | 6 | signDrop, signStep, signStepCert | no | Proven |
| Hagi.Unified.SignDescent | 25 | 1 | signScale | no | Proven |
| Hagi.Unified.StepContract | 28 | 18 | - | no | Proven |
| Hagi.Unified.StepProvider | 42 | 30 | honestQuadStep, cramDescentProvider, quadContractProvider, quadContract, honestQuadProvider | no | Proven |
| Hagi.Unified.StitchingEProcess | 9 | 1 | - | no | Proven |
| Hagi.Unified.StochasticCELearning | 47 | 13 | stepRealized, quadNoise, noiseKernel, stepNoise, thetaFun, inducedNoise, stepDrift | no | Proven |
| Hagi.Unified.StochasticLoop | 18 | 5 | - | no | Proven |
| Hagi.Unified.TelescopeInstances | 9 | 0 | - | no | Proven |
| Hagi.Unified.TernaryProbe | 7 | 3 | ternaryRoundCap, ternaryCubicStepBudget, ternaryCentralCubicProbe | no | Proven |
| Hagi.Unified.TransitionCert | 16 | 6 | toCertStepGen, toCertStep, ctContract | yes | Conditional |
| Hagi.Unified.TwoDomainConfidence | 2 | 0 | - | no | Proven |
| Hagi.Unified.VerticalCapstone | 9 | 0 | - | no | Proven |
