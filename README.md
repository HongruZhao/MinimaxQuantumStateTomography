# Minimax Quantum State Tomography

This repository contains the Lean 4 proofs of **Theorem 3** and **Corollary 4** in Hongru Zhao's paper *Minimax Quantum State Tomography with Periodic Clifford Measurements*, together with the Python simulations for the paper and supplement. The formalization covers operator norm minimum distance (OMD) and measurement weighted projected least squares (weighted PLS).

## Measurement setting

An unknown state belongs to

```math
\mathcal D_d=\{\rho\in\mathbb C^{d\times d}:\rho\succeq0,\ \mathrm{tr}\,\rho=1\},\qquad d=2^n.
```

We measure each of $T\ge1$ independent copies separately. On each copy, two layers of independent uniform Clifford gates act on a ring of $n$ qubits, with even block size $k\mid n$ and a shift of $k/2$ between layers. Computational basis measurement returns $b_t$; the recorded projector is $B_t=U_t^*|b_t\rangle\langle b_t|U_t$. Outcomes follow the Born rule. Measurement choices do not depend on earlier outcomes.

The upper bounds assume the paper's sufficient block condition

```math
\frac{92}{\ln 2}\,n\le k2^{k/2}.
```

Loss is the **full trace norm** $\|\widehat\rho-\rho\|_{\mathrm{tr}}$. The unrestricted minimax risk $R_T^*(\mathcal C)$ takes the infimum over all randomized nonadaptive single-copy measurement designs and reconstruction rules. Write $R_T^{\mathrm{per}}(\mathcal C)$ for the risk with the periodic design fixed.

## The estimators

Define the measurement channel and calibrated score by

```math
\mathcal M(A)=\mathbb E_U\sum_b\mathrm{tr}(AB_{U,b})B_{U,b},\quad
\mathcal L(A)=(d+1)\mathcal M(A)-\mathrm{tr}(A)I,\quad
\overline Y_T=\frac1T\sum_{t=1}^T((d+1)B_t-I).
```

- **OMD** minimizes $f_T(\sigma)=\|\overline Y_T-\mathcal L(\sigma)\|_{\mathrm{op}}$ over $\mathcal D_d$. A measurable feasible fit may have objective error at most $\min\{1,\sqrt{d/T}\}$.
- **Weighted PLS** minimizes $Q_T(\sigma)=\tfrac12\langle\sigma,\mathcal L(\sigma)\rangle_F-\langle\overline Y_T,\sigma\rangle_F$ over $\mathcal D_d$. The approximate-fit results use the first-order gap $g_T(\sigma)=\max_{\omega\in\mathcal D_d}\langle\mathcal L(\sigma)-\overline Y_T,\sigma-\omega\rangle_F\le\min\{1,d/T\}$. This is the measurement weighted projection of the inverse-channel estimate.

Neither estimator needs the state's rank, eigenbasis, or spectral-decay parameters.

## The results

For ordered eigenvalues, put $\tau_s(\rho)=\sum_{j>s}\lambda_j(\rho)$ and

```math
\mathcal C_{\alpha,d}(L)=\{\rho\in\mathcal D_d:\tau_s(\rho)\le Ls^{1-\alpha},\ 1\le s\le d\},
\qquad \alpha>1,\quad L\ge1.
```

**Theorem 3.** Both OMD and weighted PLS attain the spectral-class minimax rate

```math
r_{\alpha,L}(d,T)=\min\left\{1,\ L^{1/\alpha}(d/T)^{(\alpha-1)/(2\alpha)},\ \sqrt{d^3/T}\right\}.
```

Under the block condition, for either estimator,

```math
c_\alpha r_{\alpha,L}(d,T)
\le R_T^*(\mathcal C_{\alpha,d}(L))
\le R_T^{\mathrm{per}}(\mathcal C_{\alpha,d}(L))
\le \sup_{\rho\in\mathcal C_{\alpha,d}(L)}\mathbb E_\rho\|\widehat\rho-\rho\|_{\mathrm{tr}}
\le C r_{\alpha,L}(d,T).
```

Here $c_\alpha>0$ depends only on $\alpha$ and $C>0$ is universal, possibly different for the two estimators.

**Corollary 4.** For $\mathcal D_{d,r}=\{\rho\in\mathcal D_d:\mathrm{rank}(\rho)\le r\}$ and $1\le r\le d$,

```math
c\min\{1,r\sqrt{d/T}\}
\le R_T^*(\mathcal D_{d,r})
\le\sup_{\rho\in\mathcal D_{d,r}}\mathbb E_\rho\|\widehat\rho-\rho\|_{\mathrm{tr}}
\le\min\{2,Cr\sqrt{d/T}\}.
```

The constants are universal and positive. This holds for both OMD and weighted PLS under their stated fitting conditions.

The public entry point is [MainResults.lean](MainResults.lean). The original declarations are in namespace `TomographyOracleCore.PaperMatch.ExactMain`; the entry point also exposes them in `MinimaxQuantumStateTomography`.

| Declaration | Result |
| --- | --- |
| [`theorem3`](TomographyOracleCore/PaperMatch/ExactTheoremThree.lean) | Spectral minimax bounds and one OMD rule that adapts to all spectral classes. |
| [`theorem3_solver_fit`](TomographyOracleCore/PaperMatch/ExactTheoremThree.lean) | The chosen OMD rule satisfies the required fitting tolerance. |
| [`theorem3_mw_record`](TomographyOracleCore/PaperMatch/ExactSpectralMW.lean) | Spectral minimax bounds for a measurable weighted PLS fit. |
| [`corollary4`](TomographyOracleCore/PaperMatch/ExactCorollaryFour.lean) | Rank minimax bounds for the chosen OMD rule. |
| [`corollary4_omd_record`](TomographyOracleCore/PaperMatch/ExactCorollaryFourOMD.lean) | Rank minimax bounds for a measurable approximate OMD fit. |
| [`corollary4_mw`](TomographyOracleCore/PaperMatch/ExactCorollaryFourMW.lean) | Rank minimax bounds for a measurable weighted PLS fit. |

## Building and verification

The project pins **Lean 4.33.0-rc2** and Mathlib revision `641fbd329d4ffb62bef83c51f54088469056bd36`. With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
lake env lean verification/MainAxiomAudit.lean
```

The focused package includes the 504 supporting modules needed by these results. The main endpoints use only Lean's standard foundations, `propext`, `Classical.choice`, and `Quot.sound`; no additional project axiom is used. The paper's measurement, domain, and fitting hypotheses remain explicit. The full Zenodo companion contains the complete main-paper and supplement development, all endpoint inventories, and its separate storage-axiom statement. See [verification scope](docs/VERIFICATION.md).

## Python simulations

The [simulation guide](simulations/README_FIRST.md) maps the source code to Figures 2–3 and S.3–S.4. It includes the current solvers, historical benchmark drivers, sampling, configurations, plotting code, numerical checks, and the saved small-instance supplement study.

To redraw all four comparisons from the included figure summaries:

```sh
python3 -m pip install numpy matplotlib pillow
python3 simulations/publication_plotting/REPRODUCE_FIGURES.py
```

See [the solver instructions](simulations/current_local/README.md) for numerical checks and new experiments. Large historical timing inputs remain on MSI; the code and summaries are included, but the source package does not reproduce those hardware timings offline. The Python programs are numerical experiments and are separate from the Lean proofs.

## License and acknowledgments

Project contributions are copyright © 2026 Hongru Zhao and use [GPL 3.0](LICENSE). Third-party licenses and notices remain applicable; see [NOTICE](NOTICE).

The result-first presentation and separation of statements, proofs, and verification follow OpenAI's [PrimeGaps186](https://github.com/openai/PrimeGaps186) and [NavierStokesAndEuler](https://github.com/openai/NavierStokesAndEuler) repositories.
