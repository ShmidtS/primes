# PROPOSAL: simultaneous trunk+head certified step (replace per-cycle alternation)

For: the HAGI_v2 implementation agent. Written by the primes agent
(C480; theory landed in primes C475). Self-contained. All Lean
anchors are proved and frozen in primes (Freeze 8462, module
`Hagi/Training/JointTrunkHead.lean`, namespace
`Hagi.Training.JointTrunkHead`).

## (a) Context (one line)

Current: HAGI_v2 alternates extractor-freeze phases with head-only
phases (primes twin: `Hagi.Training.AlternatingJoint`,
`alternating_trajectory_bound_derived`) — the trunk moves only on
admission boundaries, and a SIMULTANEOUS (trunk, head) step had no
certificate (pin `crmsm_joint_separation`); primes C475 proved one.

## (b) Formulas and Lean anchors

Main theorem (`Hagi.Training.JointTrunkHead`):

- `joint_head_trunk_step_le` — for a joint move
  `m' = jointUpdate m bs' x t tgt` (new trunk blocks bs' AND new
  head θ' in ONE transition):

  `CE(t, lm m') ≤ CE(t, lm m) − 2A²/R² + 2·HL·dd`

  where −2A²/R² is the certified head drop on the OLD features
  (`Hagi.Model.ceOneHot_safeStep_le_residual` with
  A = `Hagi.Model.ceAlignment`, R = `Hagi.Model.ceStepRange`), and
  2·HL·dd is the trunk damage channel: CE-lip 2 in logits
  (`ce_head_lipschitz_in_logits`) × logit shift ≤ `headLip`·dd
  (`trunk_disp_logit_le`, `Hagi.Model.LMCompose.headLip`), with dd
  a MEASURED trunk displacement
  (`∀ v, |lmTrunk bs' − lmTrunk m.blocks| ≤ dd` — binder, not
  derived; honest pin).
- `joint_step_commit_strict` — if `2·HL·dd < 2A²/R²` the joint step
  STRICTLY decreases CE: the drop>0 acceptance criterion for
  `commit_drop_checked` (C463 interface, unchanged).
- Parametric trunk-displacement constants (derivable for the C465
  atoms, honest: no formula for arbitrary trunks):
  - `rms_gain_param_disp` / `provenTrunk_gain_param_disp` —
    RMSNorm-gain move: displacement ≤ √n·Σ|Δg| (saturation
    `rmsN_coord_le`: normalized output ≤ √n per coordinate);
  - `mlp_param_lip` / `certifiedMLP_param_dPre` /
    `provenTrunk_mlp_param_disp` — MLP weight move:
    ≤ n·Z·(F₁‖ΔW₂‖ + F₂‖ΔW₁‖) per position (Z = input norm,
    F₁,F₂ = Frobenius norms of the OLD/NEW weight matrices).
- Trade-off (when joint beats alternating) —
  `joint_bound_beats_alternating_bound`: over k steps, joint
  guarantee `L0 − k(2A²/R²) + k·2·HL·dd` beats the alternating
  guarantee `L0 − k·Δh + damageB` exactly when
  `k·(2A²/R² − 2·HL·dd) > k·Δh − damageB` (Δh = per-step head drop
  in the frozen-extractor regime, damageB = the alternating
  boundary damage, cf. `alternating_trajectory_bound_derived`).
  Both compared quantities are UPPER bounds on guarantees, not
  trajectories (honest pin in the docstring).

## (c) Minimal Python diff

```python
def joint_certified_step(self, batch, trunk_upd, head_upd):
    # 1) head part on OLD features (existing certified head step):
    A, R = self._alignment_range(batch)          # ceAlignment, ceStepRange
    eta = 4 * A / (R * R) if R > 0 else 1.0      # safeStepSize
    cert_head = 2 * A * A / (R * R)              # ceOneHot_safeStep_le_residual
    # 2) MEASURE the trunk displacement dd (do NOT derive it):
    logits_old = self.forward_trunk(self.blocks, batch)
    logits_new = self.forward_trunk(trunk_upd, batch)
    dd = (logits_new - logits_old).abs().amax().item() / max(HL, 1e-12)
    HL = self.head_lip(head_upd)                 # sum |headW * theta| per token
    dd = (logits_new - logits_old).abs().amax().item() / HL   # logit shift <= HL*dd
    # 3) joint certificate:
    damage = 2.0 * HL * dd
    if damage < cert_head:                       # joint_step_commit_strict
        self.blocks, self.head = trunk_upd, head_upd
        return cert_head - damage                # certified joint drop > 0
    return 0.0                                   # HOLD: keep alternating this cycle
```

## (d) Sanity numbers (primes C480, `.tmp/C480/sanity-joint-step.py`)

Toy LM, 4-vocab head over 2 features, measured trunk displacement
(shifts feature 2 by 1/20):

- R = 0.9261, A = 0.5932 ⇒ cert_head = 0.820609 (η = 2.767);
- measured logit shift ⇒ damage = 2·HL·dd = 0.100000;
- joint bound: CE_joint = −2.210826 ≤ bound = −0.124713 (holds);
- strict commit fires: damage 0.100 < cert 0.8206 ⇒ certified
  joint drop 0.7206 > 0;
- joint-vs-alternating over k = 8 cycles (alternating: Δh =
  0.7·cert_head frozen-extractor head drops, boundary damage
  damageB = 8·damage): joint net 5.765 > alt net 3.795 — the
  exact `joint_bound_beats_alternating_bound` arithmetic.

## (e) Validation criterion

Per joint-step attempt, measure the REAL CE change and require
`real_drop ≥ cert_head − damage` on EVERY committed step of a full
run (loop-5 style, same as §9). Additionally log the HOLD branch:
whenever `damage ≥ cert_head` the step must be skipped (HOLD) and
the alternating path used — count HOLDs; if HOLDs dominate (>50%
of cycles), the joint mode is not paying for this workload (honest
signal, see limits).

## (f) Honest limits

- dd is a MEASURED binder, not a derived quantity: no parametric
  trunk-displacement formula exists for arbitrary trunks (pin
  `crmsm_joint_separation` stays); only the C465 atoms
  (RMSNorm-gain, MLP weights) have derived constants — and those
  are derivable-but-not-tight.
- The cross-term (head step × trunk move interaction) is ABSORBED
  into 2·HL·dd by the triangle inequality, not cancelled: the
  damage is paid on EVERY joint step, whereas alternating pays its
  boundary damage once per k-cycle — joint wins only inside the
  `joint_bound_beats_alternating_bound` window (large A/R², small
  dd).
- The comparison theorem compares GUARANTEES (upper bounds), not
  trajectories: a dominated alternating run can still be better in
  reality; the (e) loop is the arbiter.
- The trunk-displacement measurement needs one extra forward per
  step (old-trunk vs new-trunk logits) — 2× trunk forward cost on
  joint-step batches.
