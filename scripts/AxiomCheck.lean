/-
AxiomCheck (аудит v2 §7, P0): печатает аксиомы капстоунов.
CI (ci.sh) гейтит: только [propext, Classical.choice, Quot.sound].
-/
import Hagi

#print axioms Hagi.Unified.MasterHAGI
#print axioms Hagi.Unified.grand_synthesis
#print axioms Hagi.Unified.MasterHAGICore
#print axioms Hagi.Model.wTraj_productive
#print axioms Hagi.Model.wTraj_budget_risk_invariants
#print axioms Hagi.Model.wTraj_takeoff
#print axioms Hagi.Unified.core_premises_joint_operational
#print axioms Hagi.Unified.core_premises_compress_operational
#print axioms Hagi.Model.core_premises_grow_operational
#print axioms Hagi.Examples.core_premises_merge_operational
#print axioms Hagi.Model.context_distillation_identity
#print axioms Hagi.Energy.partition_strictMono
#print axioms Hagi.Unified.certified_invariant_advance_witness
#print axioms Hagi.Foundations.trunc_premises_takeoff
#print axioms Hagi.Unified.premises_to_certified
