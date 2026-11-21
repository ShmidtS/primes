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

- modules: 537
- theorems: 12786
- defs: 4770
- noncomputable decls: 1216
- status Proven: 457 modules
- status Conditional: 25 modules
- status Empirical: 10 modules
- status Speculative: 25 modules
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
| Hagi.Autonomy.SupervisorSafety | 20 | 38 | capMember | no | Proven |
| Hagi.Autonomy.SupervisorViability | 27 | 13 | LittlestoneDim | no | Proven |
| Hagi.Autonomy.TTTStability | 2 | 0 | - | no | Proven |
| Hagi.Benchmarks | 0 | 0 | - | no | Proven |
| Hagi.Benchmarks.QuadLoopWitness | 24 | 2 | qhalf, halfStepCert | no | Proven |
| Hagi.Benchmarks.QuadraticEndToEnd | 8 | 4 | qQuantized | no | Proven |
| Hagi.Benchmarks.QuarticWitness | 29 | 12 | qFloor, w2, qDrops, qCert1, w0, qMeasured, qTraj, qBud, qE, w1, qCert2 | no | Proven |
| Hagi.Benchmarks.TernaryProbe | 7 | 3 | ternaryRoundCap, ternaryCubicStepBudget, ternaryCentralCubicProbe | no | Proven |
| Hagi.Benchmarks.TernaryWitness | 7 | 3 | ternaryStepCert, quant_jump_honest, quantOpt | no | Proven |
| Hagi.Budget.AnytimeCondensation | 3 | 0 | - | no | Proven |
| Hagi.Budget.BatchCap | 23 | 3 | batchEff, criticalS, sfoCost | no | Proven |
| Hagi.Budget.BitAlloc | 52 | 3 | layerError, totalError, totalErrorCont | no | Proven |
| Hagi.Budget.BitAllocTermination | 7 | 0 | - | no | Proven |
| Hagi.Budget.DesignOpt | 6 | 1 | wallClock | no | Proven |
| Hagi.Budget.ElementQuant | 4 | 0 | - | no | Proven |
| Hagi.Budget.IsoFrobAlloc | 2 | 1 | isoFrobSensitivity | no | Proven |
| Hagi.Budget.JointCost | 11 | 1 | nsIter | no | Proven |
| Hagi.Budget.RDAlloc | 14 | 15 | rdAllocBytes, rd_step_certified | no | Proven |
| Hagi.Budget.RankBudget | 16 | 1 | rankResidual | no | Proven |
| Hagi.Budget.ResidualVQ | 15 | 1 | - | no | Proven |
| Hagi.Budget.ThermoCondensation | 38 | 3 | log2_3, bpw, factorizedTernaryBits | no | Proven |
| Hagi.Budget.TokenWeightBias | 2 | 0 | - | no | Proven |
| Hagi.Budget.WaterFilling | 15 | 4 | effectiveCapacity, genMean, totalErrorFin, kvResidual | no | Proven |
| Hagi.Budget.WeightedExpAlloc | 22 | 4 | weightedExpBudget, weightedExpPrice, weightedExpLogCoeff, weightedExpAllocation | no | Proven |
| Hagi.Cert.Adapters | 4 | 3 | - | yes | Conditional |
| Hagi.Cert.CertifiedArgmax | 11 | 3 | avgRadius | no | Proven |
| Hagi.Cert.Core | 52 | 84 | - | no | Proven |
| Hagi.Cert.Empirical | 5 | 13 | - | no | Proven |
| Hagi.Cert.EvalBinding | 29 | 61 | - | no | Proven |
| Hagi.Cert.StepGen | 61 | 41 | - | no | Proven |
| Hagi.Cert.StepRecord | 6 | 15 | - | no | Proven |
| Hagi.Cert.Telescope | 5 | 16 | - | no | Proven |
| Hagi.Challenge.MasterChallengeV3 | 1 | 0 | - | no | Proven |
| Hagi.Challenge.MasterChallengeV4Kernel | 1 | 0 | - | no | Proven |
| Hagi.Contracts.AuditLedger | 50 | 40 | - | no | Proven |
| Hagi.Contracts.BatchCEAlignmentBudget | 30 | 2 | fixedAlignmentCesaro, rangeCurvature | no | Proven |
| Hagi.Contracts.BatchCEBestResidual | 4 | 0 | - | no | Proven |
| Hagi.Contracts.BatchCEBudgetGuard | 160 | 32 | batchParetoProblemSafeDecidable, identityParetoBatchStep, batchParetoProblem, pairMinimumNormBatchParetoProblemSafeDecidable, expandedTrainState, batchDirectionHalfTrainInput, batchCEMeasured, batchSampleCE, batchDirectionHalfTrainStep, batchParetoStepFun, guardedBatchTrainStep, asymmetricPairMinimumNormBatchStep, guardedBatchParetoStepFun, guardedBatchParetoProblemSafeDecidable, evaluatedBatchMinimumNormCert, pairMinimumNormBatchParetoProblem, minimumNormBatchParetoProblem, batchMinimumNormMinimalCert, expandedHalfTrainStep, batchMinimumNormTrainStep, minimumNormBatchParetoProblemSafeDecidable, batchPairMinimumNormTrainStep, identityMinimumNormBatchStep, asymmetricMeanBatchStep, guardedBatchParetoProblem, budgetedParetoBatchTrainStep, batchDirectionTrainStep | no | Proven |
| Hagi.Contracts.BatchCEGrowth | 194 | 80 | growthAdmissionProblemAt_decidable_safe, growthAdmissionPlanStep, growthCandidateOperationIncrement, residualDirection, residualAdmissionMargin, growthAdmissionMemoryIncrement, residualStepMargin, residualFeatures, growthCandidateStep, grownBatchState, smoothedGrowthYield, growthSelection, growthAdmissionPlanRollout, quarantinedGrowStep, growthAdmissionPlanSelection, growthProblemAt, growthAdmissionOperationIncrement, growthAdmissionSelectionTrace, growthAdmissionSelection, growthObjective, growthAdmissionSelectionPath, growthAdmissionPlanProblemAt, growthAdmissionSelectionNext, residualPath, growthAdmissionPlanProblemAt_decidable_safe, growthPath, growthProblemAt_decidable_safe, boundedGrowStep, growthSelectionNext, growthCandidateMemoryIncrement, growthAdmissionProblemAt | no | Proven |
| Hagi.Contracts.BatchCEStepCore | 47 | 13 | heterogeneousStepCert, batchDirectionTrainInput, batchPairMinimumNormTrainInput, batchTrainStepCert, batchTrainStepMinimalCert, batchCEObjective, batchTrainInput, batchTrainStep, batchLogitCertifiedDrop, batchMinimumNormTrainInput, batchCertifiedDrop, heterogeneousStep | no | Proven |
| Hagi.Contracts.BatchCETrajectory | 0 | 0 | - | no | Proven |
| Hagi.Contracts.BatchCETrajectory.Core | 53 | 0 | - | no | Proven |
| Hagi.Contracts.BatchCETrajectory.Direction | 65 | 14 | directionBatchObjective, directionBatchSampleCE, directionBatchMargin, directionBatchMeanMargin, guardedBatchInputPath, directionBatchHalfState, directionBatchState, directionBatchMinNormSquaredBudget, directionBatchHalfBindingMargin, directionBatchHalfQuadraticMargin, directionBatchHalfMeanQuadraticMargin | no | Proven |
| Hagi.Contracts.BatchCETrajectory.FixedBatch | 36 | 11 | identityScaledBatchCEPath, sameZeroInitialMeanDrop, minimumNormIdentityScaledThreshold, fixedBatchState, minimumNormIdentityInitialMeanDrop, fixedBatchObjective, identityMinimumNormScaledBatchCEPath, sameZeroScaledThreshold | no | Proven |
| Hagi.Contracts.BatchRangeBF16Cert | 18 | 3 | batchCEMetrics, batchCE_transitionStep_hold, batchCE_bf16_transitionStep_progress | no | Proven |
| Hagi.Contracts.BudgetedParetoStepCert | 6 | 1 | budgetedParetoStepCert | no | Proven |
| Hagi.Contracts.BudgetedParetoStepContract | 3 | 1 | budgetedParetoStepContract | no | Proven |
| Hagi.Contracts.CEStepCertificate | 36 | 10 | ceTrainInput, batchCEObservation, identityStepCert, identityInitialState, identityCEStep, ceTrainStepCert, ceTrainStep, ceTrainStepMinimalCert, coreCEObjective, coreParameters | no | Proven |
| Hagi.Contracts.ComputeToQuality | 14 | 1 | totalComputeProduct | no | Proven |
| Hagi.Contracts.CurriculumCert | 7 | 1 | curriculumTotal | no | Proven |
| Hagi.Contracts.DataToQuality | 13 | 1 | sampleComplexity | no | Proven |
| Hagi.Contracts.DepthExitCert | 30 | 26 | d2, d1 | no | Proven |
| Hagi.Contracts.EMTrajectory | 105 | 43 | mixtureGridWeight, mixtureModel, currentPosterior, changingEMPathDrop, changingEMPath, mixtureFamily, mixtureUnitScore, mixtureState, mixtureStateStep, mixtureJointMass, changingEMPathMGain, factorizedMixtureLabels, mixtureCanonicalPath, mixturePriorMass, changingEMPathNLL, finiteEMPathNLL, mixtureTrajectoryModel, mixtureCurrentPosterior, finiteEMPath, mixtureChannel, mixtureVectorBank, mixtureTrajectoryBank, currentPosterior, changingEMPathKLResidual | no | Proven |
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
| Hagi.Contracts.ObjectiveTrajectory | 23 | 0 | - | no | Proven |
| Hagi.Contracts.SparseInferenceCert | 28 | 8 | sparse_step_certified | no | Proven |
| Hagi.Contracts.StepCertificate | 8 | 3 | trainStepCert, trainMeasured, trainStepMinimalCert | yes | Conditional |
| Hagi.Contracts.TotalError | 5 | 0 | - | no | Proven |
| Hagi.Contracts.TruncatedSVDTail | 10 | 2 | tailCarrier, approxK | no | Proven |
| Hagi.Contracts.VilleMonitor | 24 | 16 | monitorAnchorQuiet, monitorAnchor | no | Proven |
| Hagi.Core.Ambig | 9 | 0 | - | no | Proven |
| Hagi.Core.Attention | 3 | 0 | - | no | Proven |
| Hagi.Core.BlockDiag | 3 | 1 | - | no | Proven |
| Hagi.Core.Concat | 6 | 1 | - | no | Proven |
| Hagi.Core.Element | 6 | 1 | - | no | Proven |
| Hagi.Core.ErrorProp | 17 | 8 | cascadeGain | no | Proven |
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
| Hagi.Data.AnfTransform | 51 | 31 | - | no | Proven |
| Hagi.Data.BoolVenn | 37 | 15 | signDecode, qAtom, singleAtomCE, worstMask | no | Proven |
| Hagi.Data.BytePatch | 22 | 3 | patchCount, patchSeq | no | Proven |
| Hagi.Data.DBridge | 3 | 1 | negEntropy | no | Proven |
| Hagi.Data.DField | 26 | 16 | flowMap, flowBack, epRate, divField, divField_marginal | no | Proven |
| Hagi.Data.DataMixing | 11 | 1 | mixingLoss | no | Proven |
| Hagi.Data.Distill | 48 | 4 | CE, truncNorm, crossEntropy | no | Proven |
| Hagi.Data.PACBayes | 2 | 0 | - | no | Proven |
| Hagi.Deployment.CanaryRamp | 27 | 15 | linearRamp, canary_step_certified | no | Proven |
| Hagi.Dynamics.EndpointContraction | 21 | 0 | - | no | Proven |
| Hagi.Dynamics.GrowthBridge | 89 | 12 | ignitionCeiling, ignitionGate, disMean | yes | Speculative |
| Hagi.Dynamics.ProductiveTransition | 8 | 2 | - | yes | Conditional |
| Hagi.Energy.EnergyCoordinateStep | 30 | 2 | singleCellFreeEnergy, meanFieldField | no | Proven |
| Hagi.Energy.EnergyFlow | 54 | 2 | localMeanField | no | Proven |
| Hagi.Energy.EntropyProduction | 8 | 4 | entropyProduction | no | Proven |
| Hagi.Energy.FreeEnergy | 4 | 1 | - | no | Proven |
| Hagi.Energy.Landauer | 24 | 1 | landauerUnit | yes | Empirical |
| Hagi.Energy.PairwiseCategorical | 12 | 9 | xtt, pairwiseEnergy, pairwiseInteractionSum, xex, meanFieldFreeEnergy, Bex, expectedPairwiseEnergy, Kex, oneHotState | no | Proven |
| Hagi.Energy.PoEBound | 17 | 1 | smax | no | Proven |
| Hagi.Energy.PreNorm | 5 | 0 | - | no | Proven |
| Hagi.Energy.Quantizer | 30 | 2 | gridQ, gridQVec | no | Proven |
| Hagi.Energy.STEStep | 12 | 1 | tern | yes | Empirical |
| Hagi.Energy.SingleCellDescent | 25 | 6 | transposeLocalField, Bc, localField | no | Proven |
| Hagi.Energy.Ternary | 39 | 4 | roundHalf, roundTern | no | Proven |
| Hagi.Ensemble.GapLaw | 6 | 2 | twoGap | no | Proven |
| Hagi.Ensemble.Hoeffding | 42 | 0 | - | no | Proven |
| Hagi.Ensemble.MergePrice | 29 | 20 | sigmaPrice, deltaCost, QuadModel | no | Proven |
| Hagi.Ensemble.PolicyCompatibility | 4 | 2 | integration_net_gain | yes | Conditional |
| Hagi.Ensemble.QFormerBridge | 6 | 2 | - | no | Proven |
| Hagi.Ensemble.SigmaKernel | 5 | 0 | - | no | Proven |
| Hagi.Ensemble.UniformCert | 13 | 0 | - | no | Proven |
| Hagi.External.Diversity | 4 | 0 | - | no | Proven |
| Hagi.External.Flywheel.CoherenceCharacterization | 123 | 16 | kroneckerCoherence, spectralOptimalRank1, spectralGap, effectiveRank, coherenceFactor, kroneckerErrorCoherence, normalizedSingularValueSq | no | Proven |
| Hagi.External.Flywheel.CourantFischer | 117 | 11 | rayleighQuotient, eigenvectorSpan, eigenvectorSpanTail, rayleighInf, rayleighSup, eigenvectorSpanHead | no | Proven |
| Hagi.External.Flywheel.EckartYoungLower | 1 | 0 | - | no | Proven |
| Hagi.External.Flywheel.FrobeniusNorm | 31 | 0 | - | no | Proven |
| Hagi.External.Flywheel.MDLRank | 21 | 3 | mdlErr, mdlJ, mdlDj | no | Proven |
| Hagi.External.Flywheel.MatrixNormRelations | 75 | 11 | frobeniusNorm', maxSingularValue, frobeniusNorm'', instCStarAlgebraMatrix, truncatedSVD | no | Proven |
| Hagi.External.Flywheel.NegDiagRank | 2 | 0 | - | no | Proven |
| Hagi.External.Flywheel.NormSupport | 5 | 0 | - | no | Proven |
| Hagi.External.Flywheel.SVD | 0 | 0 | - | no | Proven |
| Hagi.External.Flywheel.SVDCore | 62 | 14 | singularValues, leftSingularVectorExtended, leftSingularVectorNonzero, singularValues₀, onbToMatrix, singularDiagonal, leftUnitary, sqrtConjTransposeMulSelf, constructedU, extendedONB, leftSingularVectorEuclidean, rightUnitary | no | Proven |
| Hagi.External.Flywheel.SVDDiagonal | 8 | 0 | - | no | Proven |
| Hagi.External.Flywheel.SVDEigenvalues | 17 | 0 | - | no | Proven |
| Hagi.External.Flywheel.SVDReal | 44 | 12 | leftSingularVectorExtended_real, realAV, realSingularValues, constructedU_real, leftSingularVectorNonzero_real, onbToMatrix_real, extendedONB_real, rightOrthogonal, singularValues, leftSingularVectorEuclidean_real | no | Proven |
| Hagi.External.Flywheel.SVDRectangular | 34 | 18 | embedMinToM, leftSingularVectorNonzero_rectangular, leftUnitary, embedMinToN, rightUnitary, singularValues, finMinOfAbstract, singularValueFromEigenvalue, eigenvaluesBijection, singularDiagonal | no | Proven |
| Hagi.External.Flywheel.SVDRectangularCoherence | 32 | 4 | coherenceFactorRect, frobeniusNormRect | no | Proven |
| Hagi.External.Flywheel.SVDRectangularDecomposition | 33 | 14 | extendedONB_rectangular, leftSingularVectorEuclidean_rectangular, extendedONB_rectangular_v2, correspondingN, constructedU_rectangular, leftSingularVectorExtended_rectangular, leftSingularVectorByM, diagonalK | no | Proven |
| Hagi.External.Flywheel.SVDRectangularNorms | 15 | 4 | instCStarAlgebraMatrixLocal, maxSingularValue | no | Proven |
| Hagi.External.Flywheel.SVDRectangularOrdering | 15 | 4 | - | no | Proven |
| Hagi.External.Flywheel.SVDTruncated | 17 | 5 | truncatedSVD, truncatedSingularValues, truncatedSingularValues_tail, truncatedSVD_tail | no | Proven |
| Hagi.External.Flywheel.SpectralNormGap | 30 | 0 | - | no | Proven |
| Hagi.External.Flywheel.TruncatedSVDRank1 | 5 | 4 | - | no | Proven |
| Hagi.External.Flywheel.WeylInequality | 62 | 4 | - | no | Proven |
| Hagi.External.MemT.GDN2 | 22 | 9 | gdn2ApproxIter, gdn2Iter, gdn2Update, rowSumNorm | no | Proven |
| Hagi.Generalization.ModeState | 29 | 33 | computedGenStep, hagiPotential | yes | Empirical |
| Hagi.Geometry.SphericalSimplex | 9 | 0 | - | no | Proven |
| Hagi.Growth.CapabilityLocal | 2 | 0 | - | no | Proven |
| Hagi.Growth.FiberNecessity | 3 | 0 | - | no | Proven |
| Hagi.Growth.GainDecomposition | 25 | 24 | etaState, etaOpt, etaPolicy | no | Speculative |
| Hagi.Growth.GainRenewal | 11 | 1 | gainFromD | yes | Conditional |
| Hagi.Growth.GammaDeficit | 2 | 0 | - | no | Proven |
| Hagi.Growth.Grow | 13 | 1 | certifiedGain | yes | Conditional |
| Hagi.Growth.IntegrationOrder | 3 | 0 | - | no | Proven |
| Hagi.Growth.InterpretiveGrowth | 8 | 5 | passiveMass, pointEffect, liveMass, causalEffect | no | Proven |
| Hagi.Growth.LinearCone | 97 | 22 | sqrtGain | yes | Speculative |
| Hagi.Growth.NoiseDisentangle | 19 | 1 | avgVec | no | Proven |
| Hagi.Growth.PlasticityLedger | 10 | 3 | famMix, plasticityRadius | no | Proven |
| Hagi.Growth.Saturation | 5 | 0 | - | no | Speculative |
| Hagi.Growth.SelfDevelopment | 3 | 0 | - | no | Proven |
| Hagi.Growth.StateBinding | 6 | 2 | - | no | Speculative |
| Hagi.Growth.Takeoff | 13 | 1 | - | yes | Speculative |
| Hagi.Growth.Thermostat | 33 | 0 | - | no | Proven |
| Hagi.Information.Capacity | 11 | 3 | repRate | no | Proven |
| Hagi.Learning.ContinualForgetting | 24 | 6 | anchorLedger, adelta, atask, achain | no | Proven |
| Hagi.Learning.FOOF | 10 | 2 | foofW | no | Proven |
| Hagi.Learning.HRCN | 3 | 1 | domainTerm | no | Proven |
| Hagi.Learning.HadamardProjectors | 42 | 4 | charProj, charProjR | no | Proven |
| Hagi.Learning.RCDL | 12 | 4 | expw, weightedSoftmax | no | Proven |
| Hagi.Learning.SoftRouterMix | 67 | 20 | swWeight, sleep_anchor_loss, anchorMix, awPot, az, swLoss, mixLossOf, swMixLoss, swPredW, routerMix, ceDist | no | Proven |
| Hagi.Learning.SpectralBudget | 3 | 0 | - | no | Proven |
| Hagi.Learning.TernaryPert | 35 | 6 | layerBits, eunorm, outNorm, bitsPerTrit | no | Proven |
| Hagi.Learning.ToyTrajectory | 18 | 28 | lossS, traj | yes | Conditional |
| Hagi.Learning.TrainingTransition | 14 | 15 | taskQual, taskEnergy | no | Proven |
| Hagi.Math.Foundations.Chord | 4 | 0 | - | no | Proven |
| Hagi.Math.Foundations.ConeTakeoff | 18 | 0 | - | no | Proven |
| Hagi.Math.Foundations.GrowthBand | 4 | 0 | - | no | Proven |
| Hagi.Math.Foundations.Hoeffding | 30 | 3 | bernDenom, bernF, bernRho | no | Proven |
| Hagi.Math.Foundations.MesoScale | 4 | 0 | - | no | Proven |
| Hagi.Math.Foundations.Ortho | 4 | 0 | - | no | Proven |
| Hagi.Math.Foundations.Potential | 3 | 1 | hagiPotential | no | Proven |
| Hagi.Math.Foundations.QuadEta | 3 | 2 | quadLossAt | no | Proven |
| Hagi.Math.Foundations.Recurrence | 46 | 0 | - | no | Proven |
| Hagi.Math.Foundations.StageCalculus | 10 | 0 | - | yes | Conditional |
| Hagi.Math.Foundations.Telescope | 8 | 0 | - | no | Proven |
| Hagi.Math.Info.InfoCore | 174 | 27 | lse, ceDef, softDef, logDetShift, entropy, ceOneHot, spectralFactor, softmaxP, entDef, klDef, tvDef, logEntropyPrimitive, shannon, tvHalf, logGram | no | Proven |
| Hagi.Model.Adaptive | 20 | 1 | - | no | Proven |
| Hagi.Model.AdaptiveChunking | 50 | 12 | floorCappedChunks, adaptiveCost, floorBoundaryChunks | no | Proven |
| Hagi.Model.AlignmentRisk | 3 | 0 | - | no | Proven |
| Hagi.Model.Attention | 48 | 17 | stdIO, ropeInner, rot, flashIO, cacheFull, cacheLatent | no | Proven |
| Hagi.Model.AttentionSpend | 25 | 4 | - | no | Proven |
| Hagi.Model.AttentionTransfer | 11 | 19 | attnStack, attnGain, attnBlockBranch, attnBranch, attnBlockList | no | Proven |
| Hagi.Model.BYOL | 11 | 5 | cosS, qnorm, bl, dsum | no | Proven |
| Hagi.Model.BackboneTransfer | 18 | 2 | - | no | Proven |
| Hagi.Model.BatchCEDescent | 140 | 24 | dirRange, batchLoss, batchGradientMinimizer, batchNextParameters, batchDirectionNextParameters, batchResidualGradient, batchMajorizer, batchCommonSafeEta, batchDirectionSafeWindow, batchAlignment, batchRangeSquare, batchMeanDirection, dirAction, batchDirectionQuadraticMargin, batchSafeStep, batchFeatureRangeCoefficient, dirMajorizer, batchCommonNextParameters, meanResidualTranspose, batchMeanAction, batchCommonSafeWindow, batchDirectionMargin, batchDirectionSafeEta, alongNext | no | Proven |
| Hagi.Model.BatchCEDescentFixtures | 26 | 3 | - | no | Proven |
| Hagi.Model.BatchCEDescentHalfEta | 35 | 4 | batchDirectionHalfMargin, batchDirectionMinQuadraticMargin, batchDirectionHalfNextParameters, batchDirectionHalfEta | no | Proven |
| Hagi.Model.BatchCEDescentLogitRange | 26 | 5 | dirLogitRange, batchLogitSafeStep, batchLogitMajorizer, batchLogitRangeSquare, batchLogitNextParameters | no | Proven |
| Hagi.Model.BatchCEDescentResidualNorm | 20 | 1 | featureNormSum | no | Proven |
| Hagi.Model.BatchCEDescentStochastic | 18 | 1 | stochasticStepDraw | yes | Conditional |
| Hagi.Model.BlockNorm | 17 | 5 | globalRms, globalNorm, blockNorm, blockRms | no | Proven |
| Hagi.Model.CECoupledShortcut | 18 | 2 | shortcutScales, packedShortcutScales | no | Proven |
| Hagi.Model.CEDescent | 62 | 13 | ceAlignment, ceMajorizer, ceRangeMajorizer, ceStepLogitRange, ceLogits, ceDirection, ceRangeSafeStep, ceResidual, safeStepSize, ceNextLogits, ceNextParameters, residualTranspose, ceStepRange | no | Proven |
| Hagi.Model.CEExpansion | 10 | 4 | expandedReadoutJacobian, expandedParameters | no | Proven |
| Hagi.Model.CEGlobalConvergence | 85 | 5 | ceGrad, plStep, ceGradReg, ceReg | no | Proven |
| Hagi.Model.CEGradient | 25 | 3 | featureCLM, lseDeriv | no | Proven |
| Hagi.Model.CEGroupedScale | 89 | 24 | packedStep, blockPenalty, selectedScale, packedBlocks, groupStructuralPenalty, decodeStep, rawSuccessor, groupObservedPenalty, selectedGroupScalesExec, blockWeights, blockParameters, scalePenalty, encodedWord, quantizedBlock, featureAbsSum, packedSelected, selectedGroupScales, jointParameters | no | Proven |
| Hagi.Model.CEHeldout | 54 | 6 | decodeJoint, encodeJoint, normalizedCE, ceBound, unionConfFactor | no | Proven |
| Hagi.Model.CEJacobianMajorizer | 1 | 0 | - | no | Proven |
| Hagi.Model.CEJointScale | 45 | 16 | selectedCoupledScales, grouped_scale_choice, jointObservedPenalty, packedCoupledScales, coupledPenalty, joint_scale_choice | no | Proven |
| Hagi.Model.CEMarginPL | 99 | 9 | scalarCE, gapHead, muBall, muBallV, gapHeadGrad, sigmaV, scalarCEGrad, rho | no | Proven |
| Hagi.Model.CEMarkovConfidence | 8 | 1 | - | no | Proven |
| Hagi.Model.CEModel | 16 | 15 | singleSampleCE, batchCE | no | Proven |
| Hagi.Model.CEPadding | 67 | 10 | - | no | Proven |
| Hagi.Model.CEQuantized | 20 | 5 | ceQuantPenalty, ceQuantObservedPenalty, ternaryCEParameters, ceQuantStructuralPenalty | no | Proven |
| Hagi.Model.CEStorageBound | 4 | 0 | - | no | Proven |
| Hagi.Model.CertifiedTransition | 36 | 10 | toCertStepGen | yes | Conditional |
| Hagi.Model.ComputeOptimal | 8 | 1 | chinchillaLoss | no | Proven |
| Hagi.Model.ConsolidationMirror | 6 | 0 | - | no | Proven |
| Hagi.Model.CycleCertificate | 23 | 14 | growSeq_cycle_certificate | no | Proven |
| Hagi.Model.DiffAttention | 5 | 2 | sm, diffW | no | Proven |
| Hagi.Model.DistillCert | 13 | 16 | quantStudent | no | Proven |
| Hagi.Model.EnergyReasoning.Pseudolikelihood | 0 | 0 | - | no | Proven |
| Hagi.Model.EnergyReasoning.Pseudolikelihood.CRAM | 100 | 98 | toCertStepGen, toKernelCertStep, freeCellPseudolikelihood, toLossCeilingDrop, localFieldLogit, symmetrizeCoupling | no | Proven |
| Hagi.Model.EnergyReasoning.Pseudolikelihood.Core | 76 | 39 | conditionalDist, zstar4, pseudolikelihoodObjective, latentGradient, latentEnergy, latentQuadraticForm, heatbathWeight, heatbathKernel, latentUpdate, focusedMixture, visibleBiasWithZ, conditionalLogit, boltzmannDensity | no | Proven |
| Hagi.Model.EnergyReasoning.Pseudolikelihood.LocalField | 60 | 19 | attentionCoupling, zstar2, κa3, wa3, sparseLocalField, attentionK, Kex4, attentionWeights | no | Proven |
| Hagi.Model.EnergyReasoning.Pseudolikelihood.Mixing | 67 | 15 | yan2, vecMul, hbChain, stationaryDensity, fan2, focusedDisagreementWeight | no | Proven |
| Hagi.Model.FastArch3Transfer | 16 | 31 | fa3HeadLoss, fa3Objective, fa3BlockList, fa3Gain, fa3Stack | no | Proven |
| Hagi.Model.GDNBridge | 13 | 4 | gdnUpdate | no | Proven |
| Hagi.Model.GDNTransfer | 24 | 36 | gdnBlockBranch, gdnGain, hybStack, hybBlockList, gdnMix, gdnBlockList, hybGain, gdnGateTanh, gdnStack | yes | Conditional |
| Hagi.Model.GatedCEDescent | 108 | 25 | gatedJacobian, gatedLineObjective, gatedAlignment, gatedProjection, gatedColumnAbsSum, gatedDirection, gatedSafeDrop, gatedSecondOrderFeatureMass, gatedStepRange, gatedResidualTranspose, gatedCurvatureUniformBound, gatedCurvature, gatedNextParameters, gatedForward, gatedDisplacement, gatedFirstOrderFeatureMass, gatedAction, sechSq, gatedResidual, gatedMajorizer, gatedLogitRemainder, gatedUnitAbsLogit, gatedSafeStepSize, gatedResidualSecondOrderMass, gatedUnitSecondOrderMass | no | Proven |
| Hagi.Model.Generative | 11 | 2 | alphaBar, flowPath | no | Proven |
| Hagi.Model.Grokfast | 4 | 3 | gLow, ampDir, gHigh | no | Proven |
| Hagi.Model.HNet | 19 | 1 | hnetOptRatio | no | Proven |
| Hagi.Model.HNet2 | 11 | 3 | hier2Cost, denseCost, hier2Positions | no | Proven |
| Hagi.Model.HypothesisCompetition | 26 | 7 | dhcStep, dhcTotal, dhcOrbit, dhcWeights | no | Proven |
| Hagi.Model.LMCompose | 27 | 48 | lmLogits, lmHeadUpdate, lmFeatures, lmProbs, headLip | no | Proven |
| Hagi.Model.LabelSmoothing | 5 | 2 | lsH, lsTarget | no | Proven |
| Hagi.Model.LayerNorm | 13 | 3 | variance, mean, lnVec | no | Proven |
| Hagi.Model.Logic.VennHead | 27 | 11 | vennHead, vAtoms, relu, vAtom, venn2Head | no | Proven |
| Hagi.Model.LogitPSV | 4 | 2 | - | no | Proven |
| Hagi.Model.Losses | 29 | 6 | gnWeight, tanhE, tl, softcap, vh, nt2 | no | Proven |
| Hagi.Model.MachineBridge | 12 | 2 | machineStageInputN, machineStageInput | no | Proven |
| Hagi.Model.MambaSSM | 11 | 0 | - | no | Proven |
| Hagi.Model.MeasuredEffects | 23 | 65 | - | no | Proven |
| Hagi.Model.MeasurementCert | 11 | 13 | - | no | Proven |
| Hagi.Model.Memory | 7 | 4 | wtParams, untiedParams | no | Proven |
| Hagi.Model.Mixup | 2 | 2 | mixLabel, mixScore | no | Proven |
| Hagi.Model.ModeConnectivity | 11 | 0 | - | no | Proven |
| Hagi.Model.ModelSoup | 6 | 6 | ema | no | Proven |
| Hagi.Model.ModernHopfield | 5 | 0 | - | no | Proven |
| Hagi.Model.MuPScaling | 5 | 2 | muPUpdate | no | Proven |
| Hagi.Model.NeuralComputer | 13 | 33 | - | no | Proven |
| Hagi.Model.NonlinearCE | 29 | 5 | tanhHead, tanhHeadJ, nonlinearSafeStep, nonlinearCurvature, tanhHeadEmbedding | no | Proven |
| Hagi.Model.NormAct | 8 | 5 | swiglu, attP, sig, swish | no | Proven |
| Hagi.Model.Perceiver | 13 | 4 | - | no | Proven |
| Hagi.Model.QuantizedAdvance | 5 | 1 | - | no | Proven |
| Hagi.Model.RL | 15 | 3 | groupAdv, dpoReward, btPref | no | Proven |
| Hagi.Model.RMSNorm | 14 | 2 | ms, rnVec | no | Proven |
| Hagi.Model.RMSNormTransfer | 53 | 4 | μnEps, rnEpsEuc, rnEuc, msE | no | Proven |
| Hagi.Model.RVCore | 14 | 5 | - | no | Proven |
| Hagi.Model.RamProtocol | 30 | 24 | - | no | Proven |
| Hagi.Model.ReferenceMachine | 63 | 12 | machineStep, energyE, quantErr, quantErrNorm, energy, compressQE, compressQ, machineGap | no | Proven |
| Hagi.Model.Residual | 4 | 10 | - | no | Proven |
| Hagi.Model.ResidualVQ | 74 | 6 | latQ, refineStageEffects, reconstruct | no | Proven |
| Hagi.Model.RoPETransfer | 17 | 6 | attnRopeStack, attnRopeGain, rotEuc, attnRopeBlockList | no | Proven |
| Hagi.Model.Routing | 10 | 3 | dwScores, vstep, adv | no | Proven |
| Hagi.Model.Sidon | 6 | 1 | - | no | Proven |
| Hagi.Model.SoftmaxHead | 38 | 45 | apply, headCE, headLoss | no | Proven |
| Hagi.Model.SoftmaxStep | 26 | 2 | logitGrad, logitCE | yes | Conditional |
| Hagi.Model.SourceMixture | 4 | 3 | successDist | no | Proven |
| Hagi.Model.SpecDecoding | 15 | 4 | anchorSeq | no | Proven |
| Hagi.Model.StageSemantics | 128 | 41 | wS0, wU2, growInput, growSeq, wTraj, growTraj, wU1, wTraj2, wU0 | no | Proven |
| Hagi.Model.TanhCEStep | 25 | 3 | tanhJacobian, tanhEmbedding, tanhModel | no | Proven |
| Hagi.Numerics.Numerics | 39 | 2 | expTilt, logitMargin | no | Proven |
| Hagi.Optimization.AdaptiveCycle | 2 | 0 | - | no | Proven |
| Hagi.Optimization.Checkpoint | 2 | 0 | - | no | Proven |
| Hagi.Optimization.ComputeScaling | 11 | 0 | - | no | Proven |
| Hagi.Optimization.DREAM | 10 | 20 | - | no | Proven |
| Hagi.Optimization.DirectionPacking | 13 | 1 | Sop | no | Proven |
| Hagi.Optimization.EF21Quantizer | 20 | 4 | qTernVec | no | Proven |
| Hagi.Optimization.GraphDistanceRouting | 52 | 7 | targetRank, shortestToTargetKernel, partialShortestToTargetRows, shorterNeighborFinset | no | Proven |
| Hagi.Optimization.InexactContraction | 5 | 0 | - | no | Proven |
| Hagi.Optimization.LRSchedule | 13 | 5 | cosLR, polyStepUpdate, polyWeights, polyDelta | no | Proven |
| Hagi.Optimization.MirrorHedge | 102 | 13 | ewNorm, mirrorIterate, stepNorm, mirrorStep, ewPot, ewWeight | no | Proven |
| Hagi.Optimization.Momentum | 50 | 1 | momentumRate | no | Proven |
| Hagi.Optimization.MomentumHB | 47 | 5 | hbErr | no | Proven |
| Hagi.Optimization.NeuronAlloc | 3 | 0 | - | no | Proven |
| Hagi.Optimization.OptimizerVariants | 49 | 15 | signStep, samW, cautiousMask, norm2, adagradAcc, l2Step, fullGrad, sgn, microGrad | no | Proven |
| Hagi.Optimization.PLConvergence | 9 | 0 | - | no | Proven |
| Hagi.Optimization.RobbinsMonro | 3 | 0 | - | no | Proven |
| Hagi.Optimization.SphericalDamping | 7 | 0 | - | no | Proven |
| Hagi.Optimization.SubspaceGrowth | 6 | 1 | projResidual | no | Proven |
| Hagi.Planning.Imagination | 6 | 0 | - | yes | Conditional |
| Hagi.Pretraining.Dust | 91 | 12 | pairQ, Nrm, rademacherLaw, esEst, hcAvg, prodQ, fairBoolMeasure | no | Proven |
| Hagi.Pretraining.ProbeError | 104 | 14 | boundedProbeOptimalStep, probeGridRound, noisyCentralCubicProbe, gridCentralCubicProbe, centralCubicProbe, probeCubicEnergy, mlpResidual, probeQuadraticEnergy, probeOptimalStep, probeCost, forwardQuadraticProbe, probeCubicGrad, centralQuadraticProbe | yes | Conditional |
| Hagi.Pretraining.RobustnessLaw | 8 | 0 | - | no | Proven |
| Hagi.Pretraining.Speedrun | 15 | 1 | ceLogit | no | Proven |
| Hagi.Pretraining.SyntheticPretrain | 22 | 2 | synthGain, TimeToCapability | yes | Empirical |
| Hagi.Probability.AdaptiveSuccess | 2 | 1 | - | no | Proven |
| Hagi.Probability.Azuma | 16 | 7 | - | no | Proven |
| Hagi.Probability.CertifiedEstimator | 38 | 6 | - | no | Proven |
| Hagi.Probability.ChernoffCGF | 26 | 0 | - | no | Proven |
| Hagi.Probability.Concentration | 48 | 31 | concConfidenceTwoSided, concConfidence, concOneDrawConfidence, concRadius | no | Proven |
| Hagi.Probability.ConditionalSuccess | 18 | 1 | concDelta | yes | Empirical |
| Hagi.Probability.EntropyConvexity | 34 | 0 | - | no | Proven |
| Hagi.Probability.ExpChord | 18 | 0 | - | no | Proven |
| Hagi.Probability.FannesPinsker | 83 | 1 | dirac | no | Proven |
| Hagi.Probability.FiniteBayes | 25 | 8 | coordinateDecoder, mode, coordinateMode, observationEvidence, hammingRisk, coordinateLaw, posterior, zeroOneLoss | no | Proven |
| Hagi.Probability.FiniteEM | 29 | 2 | jointMass, mStep | no | Proven |
| Hagi.Probability.FiniteFamilyConfidence | 48 | 5 | instDecidablePredForallFinOfNatNatTwoModelGood, populationMean, twoModelP, twoModelGood | no | Proven |
| Hagi.Probability.FiniteFamilyConfidenceEmpirical | 0 | 1 | empiricalMean | no | Proven |
| Hagi.Probability.FiniteLogScore | 41 | 2 | conditionalRow | no | Proven |
| Hagi.Probability.FiniteMultiEM | 7 | 1 | batchMStep | no | Proven |
| Hagi.Probability.Freedman | 187 | 49 | historyInitial, historyAdditive, historyIncrement, historyNoise, historyLaw, stochastic_safe_step_closed, stochastic_safe_step, historyKernel, markovLaw, driftAdditive, historyCounter, pmfMean, historyCounterRate, uniformOfFinset, stochastic_safe_step_variance | yes | Empirical |
| Hagi.Probability.GibbsCooling | 46 | 0 | - | no | Proven |
| Hagi.Probability.GibbsCore | 96 | 3 | tilted, gibbsW, gibbsZ | no | Proven |
| Hagi.Probability.KLSBridge | 14 | 4 | - | no | Proven |
| Hagi.Probability.LinkedFlip | 39 | 17 | eventMask, support, uniformPlane, linkedChannel, linkedMask, changedCount | no | Proven |
| Hagi.Probability.MarkovPathSupport | 11 | 1 | - | no | Proven |
| Hagi.Probability.MirrorHedgeGibbs | 6 | 0 | - | no | Proven |
| Hagi.Probability.MirrorHedgeMWU | 84 | 4 | selectedMeanGradientMSE, selectedGradientMSE, selectedLoss_optimalPropensity, selectedLossMSE | no | Proven |
| Hagi.Probability.MomentBounds | 16 | 0 | - | no | Proven |
| Hagi.Probability.NoiseTemperature | 61 | 5 | popVar, popMean, batchMean, uniP, centered | no | Proven |
| Hagi.Probability.PMFBridge | 10 | 6 | - | no | Proven |
| Hagi.Probability.RankedStopRouting | 33 | 18 | classifyRouting | no | Proven |
| Hagi.Probability.SphericalAngle | 57 | 1 | sphericalAngle | no | Proven |
| Hagi.Probability.StationaryFlatness | 10 | 2 | expectNat, probGe | no | Proven |
| Hagi.Probability.Substrate | 7 | 0 | - | no | Proven |
| Hagi.Probability.ThermoBridge | 32 | 5 | snr, stepCost, gainPerCost, criticalBatch, batchGain | no | Proven |
| Hagi.Research | 0 | 0 | - | no | Proven |
| Hagi.Research.Ceilings | 15 | 1 | - | no | Speculative |
| Hagi.Research.ChainUnification | 9 | 0 | - | no | Speculative |
| Hagi.Research.ConditionalInformation | 33 | 4 | conditionalMutualInformation | no | Speculative |
| Hagi.Research.CrossModalGap | 10 | 3 | crossModalGap | no | Speculative |
| Hagi.Research.Legacy | 0 | 0 | - | no | Speculative |
| Hagi.Research.Legacy.AdvanceWitness | 3 | 0 | - | yes | Deprecated |
| Hagi.Research.Legacy.ArchitectureTheorem | 79 | 9 | forwardKlTarget, reverseKlTarget, l1Norm, binEnt, distillEfficiency | yes | Deprecated |
| Hagi.Research.Legacy.Assumptions | 29 | 16 | trunc_idle_witness, idleTraj | yes | Deprecated |
| Hagi.Research.Legacy.CertifiedGrowth | 6 | 0 | - | no | Deprecated |
| Hagi.Research.Legacy.CorePremisesDerived | 6 | 0 | - | yes | Deprecated |
| Hagi.Research.Legacy.GrandSynthesis | 6 | 1 | - | no | Deprecated |
| Hagi.Research.Legacy.HAGICertWitness | 6 | 2 | witnessTraj, witnessState | no | Deprecated |
| Hagi.Research.Legacy.LearningKernel | 5 | 3 | - | no | Deprecated |
| Hagi.Research.Legacy.LinkedWitness | 2 | 1 | - | no | Deprecated |
| Hagi.Research.Legacy.MasterChallenge | 1 | 0 | - | no | Deprecated |
| Hagi.Research.Legacy.MasterHAGI | 18 | 5 | - | yes | Deprecated |
| Hagi.Research.Legacy.MasterHAGICoupled | 21 | 11 | coupledGrowthTraj | no | Deprecated |
| Hagi.Research.Legacy.MasterHAGITrunc | 20 | 0 | - | yes | Deprecated |
| Hagi.Research.Legacy.Nonvacuity | 72 | 14 | Spos, Spos', MwEffects, S₀, Mw0, mergeOperationalCertStep, mergeStrictCertStep, S₁, jensenGap, Mw, witnessGap | yes | Deprecated |
| Hagi.Research.Legacy.NonvacuityHorizon | 6 | 2 | satF, satC | no | Deprecated |
| Hagi.Research.Legacy.QuadraticConcrete | 17 | 4 | quadGen, quadE, quadGen', quadState | no | Deprecated |
| Hagi.Research.Legacy.RecursiveGrowth | 24 | 0 | - | yes | Deprecated |
| Hagi.Research.Legacy.StateTakeoff | 4 | 0 | - | yes | Deprecated |
| Hagi.Research.Legacy.TernaryGrad | 6 | 0 | - | no | Deprecated |
| Hagi.Research.Legacy.TopLevel | 15 | 0 | - | yes | Deprecated |
| Hagi.Research.MarkovPercolation | 22 | 7 | weightedNeighborKernel, maskedNeighborWeights, neighborOrStayKernel, uniformNeighborKernel | no | Speculative |
| Hagi.Research.OmniInvariant | 10 | 2 | - | no | Speculative |
| Hagi.Research.OmniState | 12 | 2 | - | no | Speculative |
| Hagi.Research.PPT | 41 | 16 | goodSet, pptTarget, pptSwapKernel, pptNorm, pptSwapAccept | yes | Speculative |
| Hagi.Research.PPTCanonical | 2 | 0 | - | no | Speculative |
| Hagi.Research.RecursiveSelfDevelopment | 5 | 1 | realizedSuccess | no | Speculative |
| Hagi.Research.RoundViability | 3 | 0 | - | no | Speculative |
| Hagi.Research.RsiCriterion | 9 | 0 | - | no | Speculative |
| Hagi.Research.Schelling | 12 | 3 | localCompatibleDegree, locallySatisfied | no | Speculative |
| Hagi.Research.SchellingCandidateSelection | 1 | 2 | - | no | Speculative |
| Hagi.Research.SchellingMarkovRouting | 2 | 0 | - | no | Speculative |
| Hagi.Research.SchellingPercolation | 11 | 0 | - | no | Speculative |
| Hagi.Research.SeedOnly | 7 | 0 | - | yes | Speculative |
| Hagi.Research.Site | 29 | 22 | percolationSystem, R | no | Speculative |
| Hagi.Runtime.BF16Delta | 74 | 30 | - | no | Proven |
| Hagi.Runtime.CertChecker | 17 | 27 | - | no | Proven |
| Hagi.Runtime.ControllerGates | 38 | 1 | - | no | Proven |
| Hagi.Runtime.TernaryExact | 61 | 17 | dyadicLevel, ternaryValueEncode, satTail, quantMat, packedTernarySamples, ternaryValueDecode, qTern | yes | Conditional |
| Hagi.Runtime.VennPacking | 15 | 4 | vennTritRow, rowByte, rowWord | no | Proven |
| Hagi.Semantics.CanonicalParams | 4 | 4 | canonWeights | no | Proven |
| Hagi.Semantics.DerivedStateCoherence | 5 | 1 | derivedProj | no | Proven |
| Hagi.Semantics.FunctionalState | 6 | 16 | fsCapa, fsEnergy, funStep, funStepJoint | no | Proven |
| Hagi.Semantics.MemorySemantics | 15 | 21 | ramWriteCert_of_updateRow | no | Proven |
| Hagi.Semantics.Split | 23 | 27 | ceOneHotObjective, linearHeadSpec | no | Proven |
| Hagi.Semantics.StateUnification | 14 | 6 | canonicalTrainStep | no | Proven |
| Hagi.Sparsity.SparseStep0 | 1 | 0 | - | no | Proven |
| Hagi.Spectral.RankGrowth | 2 | 2 | - | no | Proven |
| Hagi.StatMech.Hopfield.CharPatterns | 12 | 3 | sylvesterRR, charEnergy | no | Proven |
| Hagi.StatMech.Hopfield.Concentration | 12 | 0 | - | no | Proven |
| Hagi.StatMech.Hopfield.LowerBound | 4 | 0 | - | no | Proven |
| Hagi.StatMech.Hopfield.Model | 3 | 5 | partition, freeEnergyDensity, energy | no | Proven |
| Hagi.StatMech.Hopfield.SubMemory | 12 | 1 | subsetEnergy | no | Proven |
| Hagi.State.CanonicalTrainState | 21 | 45 | trainMetrics | no | Proven |
| Hagi.State.EvalBindingCert | 9 | 12 | canonicalEval | no | Proven |
| Hagi.State.MemoryCycle | 43 | 36 | frobNorm | no | Proven |
| Hagi.State.TrainState | 19 | 90 | qualityScalar | no | Proven |
| Hagi.State.TrainTrajectory | 28 | 38 | stepDrop, stepExecErr, stepDrop | no | Proven |
| Hagi.State.Transition | 25 | 35 | lossOf, trainStep, guidedTrainStep | no | Proven |
| Hagi.State.Views | 3 | 1 | - | no | Proven |
| Hagi.Step.ArmijoAcceptance | 9 | 0 | - | no | Proven |
| Hagi.Step.BatchBudget | 10 | 0 | - | no | Proven |
| Hagi.Step.CPUFreeze | 4 | 1 | - | no | Proven |
| Hagi.Step.CausalFilter | 28 | 17 | - | no | Proven |
| Hagi.Step.Compound | 6 | 0 | - | yes | Empirical |
| Hagi.Step.DirectionProvider | 15 | 20 | signProvider, kktComplementarity, kktPrimalResidual, kktStationarity | yes | Conditional |
| Hagi.Step.Dominate | 6 | 0 | - | no | Proven |
| Hagi.Step.ErrorFeedback | 22 | 4 | - | no | Proven |
| Hagi.Step.FrobeniusLMO | 13 | 0 | - | no | Proven |
| Hagi.Step.GPM | 5 | 3 | - | no | Proven |
| Hagi.Step.GradCentralization | 4 | 1 | gc | no | Proven |
| Hagi.Step.GradClip | 5 | 1 | clip | no | Proven |
| Hagi.Step.HybridState | 3 | 0 | - | no | Proven |
| Hagi.Step.Joint | 4 | 1 | quadIncr | no | Proven |
| Hagi.Step.JointPreserve | 6 | 0 | - | no | Proven |
| Hagi.Step.LazyAdam | 7 | 0 | - | no | Proven |
| Hagi.Step.LiveDeltaSafe | 6 | 2 | - | no | Proven |
| Hagi.Step.MDLThreeCurrency | 10 | 5 | dataCodeLen, sourceEntropy | no | Proven |
| Hagi.Step.Muon | 30 | 3 | ns | no | Proven |
| Hagi.Step.NCEExact | 25 | 5 | impW, secondMomentW, qMean, secondMoment, partZ | no | Proven |
| Hagi.Step.NewtonSchulzMatrix | 38 | 5 | newtonIter, nsMatrixStep, newtonStep, nsStep, nsIter | no | Proven |
| Hagi.Step.NoisyPL | 17 | 0 | - | no | Proven |
| Hagi.Step.PreconditionerDescent | 9 | 0 | - | no | Proven |
| Hagi.Step.ProjectionDescent | 26 | 2 | segmentMinNormCoefficient, segmentMinNorm | yes | Conditional |
| Hagi.Step.RiemannNewtonPolar | 8 | 0 | - | no | Proven |
| Hagi.Step.RobustDescent | 3 | 0 | - | no | Proven |
| Hagi.Step.SNRWeights | 9 | 0 | - | no | Proven |
| Hagi.Step.SafeQP | 89 | 14 | transportedGrad, noiseEps, adaptiveNoiseEps, latticeStep, latticeNet | yes | Empirical |
| Hagi.Step.SafeQPStep | 36 | 3 | safeqpEtaMax, safeqpEtaMaxConflictFree | yes | Conditional |
| Hagi.Step.SignSGD | 5 | 1 | sgn1 | no | Proven |
| Hagi.Step.Upgrades | 19 | 3 | nce_per_sample_corrected, softmaxW | no | Proven |
| Hagi.Step.WarmupSchedule | 5 | 1 | warmupEta | no | Proven |
| Hagi.Step.WeightDecay | 8 | 0 | - | no | Proven |
| Hagi.System.Certificates | 33 | 69 | - | no | Proven |
| Hagi.System.DerivedState | 21 | 16 | smoothL, energyOf, derivedEffects, derivedGrowthState, gradOf | no | Proven |
| Hagi.System.GrowthState | 87 | 201 | growthQuad, witEffects, witState, stageCertificate, witParams, gainJoint, verify, costCompress | yes | Conditional |
| Hagi.System.StepCertificate | 12 | 17 | bestFeasibleDecrease, toCertStepGen, stepCertificateOfParts, instDecidablePredStepCertificateStepFeasible | no | Proven |
| Hagi.System.UnifiedStep | 3 | 0 | - | no | Proven |
| Hagi.Theory.AdapterGrowth | 14 | 4 | rankSelect, rankScore, adapterStep | no | Proven |
| Hagi.Theory.AdaptiveMajorizer | 59 | 4 | ceAdaptiveCurv, ceAdaptiveCurvTight, varWeight, kappa | no | Proven |
| Hagi.Theory.AnytimeHoldoutStop | 13 | 4 | eProcess | no | Proven |
| Hagi.Theory.BlockAdmission | 23 | 23 | - | no | Proven |
| Hagi.Theory.BlockLipschitz | 48 | 9 | relu, mlpApply, rmsDen, attAgg, rmsN, certifiedConvAtt, attW, certifiedRMSNorm, certifiedMLP | no | Proven |
| Hagi.Theory.CEChain | 60 | 18 | gatedStep, batchStep, universalDrop, singleSampleStep, universalStepSize | no | Proven |
| Hagi.Theory.CertCEHoldout | 2 | 1 | - | no | Proven |
| Hagi.Theory.CertSandwichBench | 2 | 0 | - | no | Proven |
| Hagi.Theory.CertifyThenCommit | 29 | 35 | - | no | Proven |
| Hagi.Theory.Compression | 52 | 9 | thrComp, signComp | no | Proven |
| Hagi.Theory.Continual | 30 | 22 | agemStep, nrm, sigmaTail, hybridSelect, hybridStep | no | Proven |
| Hagi.Theory.FlowMatching | 14 | 7 | cfmLoss, cfmLinStep, cfmJoint, cfmSampleLoss, cfmOtField | no | Proven |
| Hagi.Theory.FullPipeline | 18 | 40 | - | no | Proven |
| Hagi.Theory.FunctionPreservingGrowth | 17 | 3 | - | no | Proven |
| Hagi.Theory.GaugeQuotient | 17 | 16 | quotientResidual, seq, rot | no | Proven |
| Hagi.Theory.GrowSnap | 3 | 0 | - | no | Proven |
| Hagi.Theory.GrowTrunkBlock | 9 | 2 | - | no | Proven |
| Hagi.Theory.HadamardIncoherence | 22 | 6 | - | no | Proven |
| Hagi.Theory.Interpretability | 14 | 18 | instFintypeGoodSet | no | Proven |
| Hagi.Theory.LogitGrowth | 43 | 11 | step, trajectory, orbit, initial, next, unitEta, measuredInput | no | Proven |
| Hagi.Theory.MDLPrune | 20 | 3 | - | no | Proven |
| Hagi.Theory.MasterEF | 14 | 18 | - | yes | Conditional |
| Hagi.Theory.MasterTheorem | 46 | 31 | stepPenalty, stepCost, stepDrop | no | Proven |
| Hagi.Theory.MergeQuant | 46 | 12 | curvRemainder, quadLoss, mid, quadLossDiag | no | Proven |
| Hagi.Theory.MiniHagi | 3 | 1 | miniHagiCanonical | no | Proven |
| Hagi.Theory.MiniHagi2 | 3 | 1 | miniHagi2Canonical | no | Proven |
| Hagi.Theory.OnlinePL | 28 | 0 | - | no | Proven |
| Hagi.Theory.ProvenTrunk | 11 | 5 | witnessW, provenBlocks, trunkLip, concreteLM, witnessG | no | Proven |
| Hagi.Theory.RollbackGate | 22 | 44 | - | no | Proven |
| Hagi.Theory.SafeStep | 72 | 43 | instDecidableAcceptCondition, ternaryCompress, certifiedDrop, dist2, proposalMetrics, safeStepMap, acceptStepCert, stochastic_safe_step_certificate, compressedCertifiedDrop, certifiedStepSize | no | Proven |
| Hagi.Theory.SelfEdit | 43 | 21 | vel, clampIdx, idxTraj, qround | no | Proven |
| Hagi.Theory.Softmax | 52 | 7 | auxG, bandWidth, sandwichMid | no | Proven |
| Hagi.Theory.Statistics | 164 | 18 | popMean, sigWR, wrPopMean, muCond, qdWR, popDens, holdoutMean, wrMean, wrPopVar, wrX, wrM, cSc | no | Proven |
| Hagi.Theory.TrainerBenchmark | 7 | 3 | loTB, hiTB | no | Proven |
| Hagi.Training.AdaptiveAnytime | 21 | 15 | adaptiveRoundWeights | no | Proven |
| Hagi.Training.Admission | 25 | 34 | admissionMargin, admitRule | yes | Conditional |
| Hagi.Training.AlternatingJoint | 77 | 100 | stepPenalty, stepDamage, derivedStepDamage, stepDrop', stepPenalty', stepDrop | no | Proven |
| Hagi.Training.CRMSM | 35 | 98 | blockGram | no | Proven |
| Hagi.Training.Ctv2Telescope | 22 | 7 | protoMeasured, stepDrop, scOf, ecToSc, ctv2Honest, smToExec | yes | Conditional |
| Hagi.Training.ExecutedCert | 16 | 14 | toRecord, toCertStep, toCertStepGen | no | Proven |
| Hagi.Training.GrowthComputedCert | 3 | 2 | next, stepCert | no | Proven |
| Hagi.Training.JointTrunkHead | 18 | 1 | jointUpdate | no | Proven |
| Hagi.Training.MacroStatCert | 32 | 36 | macroDecide, macroCertAnchor | no | Proven |
| Hagi.Training.ModelComparison | 18 | 16 | zIndicator, zOf, Score, modelGap | no | Proven |
| Hagi.Training.StepProvider | 42 | 30 | honestQuadStep, cramDescentProvider, quadContractProvider, quadContract, honestQuadProvider | no | Proven |
| Hagi.Training.TTCAT | 18 | 32 | - | no | Proven |
| Hagi.Training.TransitionCert | 22 | 37 | - | no | Proven |
| Hagi.Unified.AnytimeMartingale | 32 | 0 | - | yes | Empirical |
| Hagi.Unified.CandidateConfig | 16 | 20 | - | no | Proven |
| Hagi.Unified.CertifiedLoop | 71 | 35 | anchorB, anchorStep0, anchorStep1, anchorObl, anchorObj, anchorW, anchorKm, anchorChain | no | Proven |
| Hagi.Unified.CertifiedTrajectory | 2 | 0 | - | no | Proven |
| Hagi.Unified.CommitGate | 16 | 20 | gateDecision, toCertStepGen, instDecidableGate | no | Proven |
| Hagi.Unified.CostComposition | 13 | 2 | - | no | Proven |
| Hagi.Unified.CountableStitching | 10 | 1 | stitchedMasterCountable | no | Proven |
| Hagi.Unified.DerivAlong | 17 | 0 | - | yes | Conditional |
| Hagi.Unified.DescentCore | 6 | 15 | nrm2, inprod | no | Proven |
| Hagi.Unified.DescentCoreDiag | 14 | 4 | diagE, diagObjective | no | Proven |
| Hagi.Unified.DescentCoreQuad | 11 | 3 | quadE, quadObjective | no | Proven |
| Hagi.Unified.Distillation | 13 | 2 | binEntropy, softProb | no | Proven |
| Hagi.Unified.EmpiricalPremises | 7 | 16 | - | no | Proven |
| Hagi.Unified.FiniteMeasureBridge | 4 | 0 | - | no | Proven |
| Hagi.Unified.HonestTransition | 18 | 16 | quadObj | no | Proven |
| Hagi.Unified.LinkedProjects | 1 | 0 | - | no | Proven |
| Hagi.Unified.LinkedQVec | 10 | 26 | qgen | no | Proven |
| Hagi.Unified.LiveDeltaCycle | 10 | 25 | - | no | Proven |
| Hagi.Unified.Liveness | 3 | 0 | - | no | Proven |
| Hagi.Unified.LogitCert | 12 | 6 | logitStepCert', logitStepCert, logitStepCertExact', logitStepCertExactCore, logitMeasured, logitStepCertExact | yes | Conditional |
| Hagi.Unified.LoopInstances | 11 | 7 | quadStepCert, quadFloor, quadMeasured, quadCert | no | Proven |
| Hagi.Unified.MachineProto | 23 | 20 | fsTraj, fsGate, evalCapa, machineProto | no | Proven |
| Hagi.Unified.MicroStepCert | 4 | 2 | - | no | Proven |
| Hagi.Unified.NCStepCert | 20 | 6 | ncContract, ncTraj, ncStepCert, ncMinimalStepCert, ncCertStep, ncMeasured | no | Proven |
| Hagi.Unified.NegativeTests | 6 | 0 | - | no | Proven |
| Hagi.Unified.ParetoExecution | 0 | 0 | - | no | Proven |
| Hagi.Unified.ParetoExecution.Controller | 112 | 59 | minimumResource, guardedMinimumResource, logitEstimate, estimatedMaxValue, logitProblem, logitTrajCert, logitProblemSafeDecidable, guardedLogitNext, logitStepFun, logitSafeDecidable, robustMinimumResource | no | Proven |
| Hagi.Unified.ParetoExecution.Selection | 42 | 27 | guardedRobustNext, robustNext, selection, selectedNext, selectionIn, scoreDominatingIn | no | Proven |
| Hagi.Unified.ParetoExecution.Trajectory | 93 | 14 | fixedBiasBinaryPath, scaledBiasBinaryValueEstimate, scaledBiasBinaryPath, scaledBiasBinaryProgressCount, inverseScaledController, fixedBiasBinaryValueEstimate, fixedBiasBinaryGain, guardedRobustPath, guardedRobustGain, scaledBiasBinaryGain, fixedBiasBinaryProgressCount | no | Proven |
| Hagi.Unified.QuadMachine | 19 | 9 | machineCert, commitInd, commitCount, gateTraj, quantLift, gateStep | no | Proven |
| Hagi.Unified.RateTheory | 24 | 6 | - | no | Proven |
| Hagi.Unified.RecursiveClean | 19 | 21 | timeConsistency, piR, indepMass, branchLocality | no | Proven |
| Hagi.Unified.SignComp | 22 | 6 | signDrop, signStep, signStepCert | no | Proven |
| Hagi.Unified.SignDescent | 25 | 1 | signScale | no | Proven |
| Hagi.Unified.StepContract | 28 | 18 | - | no | Proven |
| Hagi.Unified.StitchingEProcess | 9 | 1 | - | no | Proven |
| Hagi.Unified.StochasticCELearning | 44 | 12 | stepRealized, quadNoise, noiseKernel, stepNoise, thetaFun, inducedNoise, stepDrift | no | Proven |
| Hagi.Unified.StochasticLoop | 18 | 5 | - | no | Proven |
| Hagi.Unified.TransitionCert | 16 | 7 | toCertStepGen, toCertStep, ctContract, toRecord | yes | Conditional |
