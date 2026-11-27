# Research note: NTK balance and quantization error (cycle 88)

Source: ask.sciencemadereadable.com query «balancing NTK eigenvalues — quantization
error». No paper studies the link directly. Relevant evidence:

* Cai et al. 2024 (arXiv:2407.17834): batch/layer normalisation *reduce the
  maximum and the variance of NTK eigenvalues*, shifting the spectrum upward and
  alleviating spectral bias. Gauge balance acts on the same object for a rank-1
  factor: in the linearised regime the contribution of factor `B·A` to the
  kernel is bounded by `‖B‖²·‖A‖²` (`ResidualVQ.frobSq_mul_le`), and the
  *quantization noise* injected into the output by each factor is bounded by
  the squared norm of its partner — so the sum of the two noise terms is
  `(c‖B‖)²·e + (‖A‖/c)²·e`, minimised exactly at the gauge `c² = ‖A‖/‖B‖`
  (`GaugeBalance.balance_key`, AM-GM). This is the content of the prototype's
  «Gauge + NTK-Reg» combination: NTK-Reg penalises the top of the spectrum,
  gauge balance minimises the noise term at fixed function.
* Zhang, Yin, Wang 2022 (arXiv:2206.05916): under stochastic rounding the NTK
  of a binary-weight network has exponentially decaying eigenvalues — its RKHS
  is a strict subset. Quantization noise is *not* isotropic in function space;
  it removes the high-eigenvalue directions first. A dead block (`W_down = 0`)
  is the extreme case: its gradient direction is absent from the kernel
  entirely (`GaugeBalance.dead_loss_const`).

Conclusion: no new theorem needed — `balance_key` + `frobSq_mul_le` already
cover the linear-regime claim; the spectral statement (variance of eigenvalues)
is not formalised. Priority stays with the code-side: MLA factor in
`gauge_balance` (PROPOSAL 25 addendum) and a `max_eig` log for the NTK term.
