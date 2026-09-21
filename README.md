# Minimax Quantum State Tomography

This repository contains the Lean 4 proofs of **Theorem 3** and **Corollary 4** in Hongru Zhao's paper *Minimax Quantum State Tomography with Periodic Clifford Measurements*, together with the Python simulations for the paper and supplement. The formalization covers operator norm minimum distance (OMD) and measurement weighted projected least squares (weighted PLS).

Quantum state tomography reconstructs an unknown quantum state from measurement outcomes. The question here is how the reconstruction error depends on the number of measured copies, the system dimension, and the decay of the state's eigenvalues. The results give matching upper and lower bounds on the worst-case expected error, while the reconstruction methods require no advance knowledge of the state's rank or spectral decay.

## Measurement setting

### States and observations

A qubit is a two-level quantum system, so a system of $n$ qubits has dimension $d=2^n$. Its state is represented by a **density matrix**: a positive semidefinite Hermitian matrix with trace one. Positivity makes its eigenvalues nonnegative, and the trace condition makes them sum to one. A rank-one state is pure; a state of higher rank is mixed.

An unknown state belongs to

```math
\mathcal D_d=\{\rho\in\mathbb C^{d\times d}:\rho\succeq0,\ \mathrm{tr}\,\rho=1\},\qquad d=2^n.
```

We measure each of $T\ge1$ independent copies separately. On each copy, two layers of independent uniform Clifford gates act on a ring of $n$ qubits, with even block size $k\mid n$ and a shift of $k/2$ between layers. Computational basis measurement returns $b_t$; the recorded projector is $B_t=U_t^*|b_t\rangle\langle b_t|U_t$. Outcomes follow the Born rule. Measurement choices do not depend on earlier outcomes.

Here $U_t$ is the sampled circuit, $b_t$ is an observed $n$-bit string, and the star denotes conjugate transpose. The pair $(U_t,b_t)$ determines $B_t$, the rank-one projector onto the corresponding measurement direction. The probability of that outcome is

```math
p_\rho(b\mid U)=\mathrm{tr}(\rho B_{U,b}).
```

### What are Clifford gates?

The single-qubit Pauli operators are $X$, $Y$, and $Z$: $X$ swaps the computational basis states, $Z$ changes the sign of the state $|1\rangle$, and $Y=iXZ$. Together with the identity $I$, their tensor products form **Pauli strings**. Including the phases $1,i,-1,-i$ gives the $k$-qubit Pauli group

```math
\mathcal P_k=\{i^a P_1\otimes\cdots\otimes P_k:
a\in\{0,1,2,3\},\ P_j\in\{I,X,Y,Z\}\}.
```

A **Clifford gate** on $k$ qubits is a unitary matrix $G$ that preserves this group under conjugation:

```math
G\mathcal P_kG^*=\mathcal P_k.
```

Thus it sends each Pauli string to another Pauli string, up to phase. Familiar Clifford gates include the Hadamard gate, the phase gate $S$, and controlled-NOT; these generate Clifford circuits. Global phases do not affect measurement probabilities, so a **uniform Clifford gate** here is sampled uniformly from the finite Clifford group after identifying gates that differ only by a global phase.

### The periodic two-layer experiment

Each layer partitions the qubit ring into $n/k$ disjoint blocks of $k$ qubits and applies an independent random Clifford gate to every block. The first layer uses blocks shifted by $k/2$ relative to the second layer. When $k<n$, overlapping blocks in different layers share $k/2$ qubits. When $k=n$, both layers act on the entire system. The ring wraps around at its ends. Both layers are resampled independently for every measured copy. The two-layer description counts operations on whole $k$-qubit blocks; each block can contain several elementary gates.

The upper bounds assume the paper's sufficient block condition

```math
\frac{92}{\ln 2}\,n\le k2^{k/2}.
```

### Loss and minimax risk

Loss is the **full trace norm** $\|\widehat\rho-\rho\|_{\mathrm{tr}}$, the sum of the singular values of the estimation error. It lies between zero and two for density matrices and equals twice the conventional trace distance.

For a specified class of states $\mathcal C$, the unrestricted minimax risk is

```math
R_T^*(\mathcal C)=\inf_{(\Pi,\widehat\rho)}\sup_{\rho\in\mathcal C}
\mathbb E_{\rho,\Pi}\|\widehat\rho-\rho\|_{\mathrm{tr}}.
```

The supremum selects the hardest state in the class. The infimum chooses the best measurement design $\Pi$ and reconstruction rule, which may use knowledge of the class but not of the unknown state. The expectation averages over the measurement settings, outcomes, and any reconstruction randomness. Admissible designs use separate measurements on individual copies, with the full sequence of settings selected before any outcomes are observed; this is the **randomized nonadaptive single-copy** model. Write $R_T^{\mathrm{per}}(\mathcal C)$ for the risk when the periodic design is fixed and only the reconstruction rule is optimized.

## The estimators

Define the measurement channel and calibrated score by

```math
\mathcal M(A)=\mathbb E_U\sum_b\mathrm{tr}(AB_{U,b})B_{U,b},\quad
\mathcal L(A)=(d+1)\mathcal M(A)-\mathrm{tr}(A)I,\quad
\overline Y_T=\frac1T\sum_{t=1}^T((d+1)B_t-I).
```

The channel $\mathcal M$ describes how the measurement ensemble maps a matrix to its average observed projector. In particular, $\mathbb E_\rho\overline Y_T=\mathcal L(\rho)$. Both estimators fit this observable quantity while requiring the estimate to remain a density matrix. For Hermitian matrices, the operator norm is the largest absolute eigenvalue, and the Frobenius inner product is $\langle A,B\rangle_F=\mathrm{tr}(AB)$.

- **OMD** minimizes $f_T(\sigma)=\|\overline Y_T-\mathcal L(\sigma)\|_{\mathrm{op}}$ over $\mathcal D_d$. A measurable feasible fit may have objective error at most $\min\{1,\sqrt{d/T}\}$.
- **Weighted PLS** minimizes $Q_T(\sigma)=\tfrac12\langle\sigma,\mathcal L(\sigma)\rangle_F-\langle\overline Y_T,\sigma\rangle_F$ over $\mathcal D_d$. The approximate-fit results use the first-order gap $g_T(\sigma)=\max_{\omega\in\mathcal D_d}\langle\mathcal L(\sigma)-\overline Y_T,\sigma-\omega\rangle_F\le\min\{1,d/T\}$. This is the measurement weighted projection of the inverse-channel estimate.

Neither estimator needs the state's rank, eigenbasis, or spectral-decay parameters.

## The results

### The spectral-decay class

The parameter class is a family of density matrices specified by their eigenvalues. Write them in decreasing order as

```math
\lambda_1(\rho)\ge\lambda_2(\rho)\ge\cdots\ge\lambda_d(\rho)\ge0,
\qquad \sum_{j=1}^d\lambda_j(\rho)=1.
```

For ordered eigenvalues, put $\tau_s(\rho)=\sum_{j>s}\lambda_j(\rho)$ and

```math
\mathcal C_{\alpha,d}(L)=\{\rho\in\mathcal D_d:\tau_s(\rho)\le Ls^{1-\alpha},\ 1\le s\le d\},
\qquad \alpha>1,\quad L\ge1.
```

The **spectral tail** $\tau_s(\rho)$ is the total eigenvalue mass left after retaining the largest $s$ eigenvalues. Membership in $\mathcal C_{\alpha,d}(L)$ requires the displayed tail bound at **every integer cutoff** $1\le s\le d$.

- $\alpha$ controls how quickly the tail must decrease: larger $\alpha$ imposes faster decay.
- $L$ controls the allowed tail size: larger $L$ permits a larger class of states.
- $d$ is the matrix dimension. The eigenbasis is arbitrary, so the class is invariant under unitary changes of basis.

For example, $\alpha=2$ and $L=1$ require $\tau_s(\rho)\le1/s$. When $d\ge10$, at most one tenth of the state's eigenvalue mass may lie beyond its ten largest eigenvalues. Such a state can still have full rank: the condition describes how well it can be approximated by a lower-rank state. More precisely, the smallest full trace norm error among rank-at-most-$s$ density matrix approximations is $2\tau_s(\rho)$. Polynomial decay of individual eigenvalues also gives polynomial tail decay: if $\lambda_j(\rho)\le A j^{-\alpha}$, then $\tau_s(\rho)\le A s^{1-\alpha}/(\alpha-1)$.

### Theorem 3: optimal rates over spectral-decay classes

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

The lower bound says that every admissible measurement-and-reconstruction procedure has a state in the class on which its expected error is at least a constant times the stated rate. The upper bound says that OMD and weighted PLS attain that rate using the periodic Clifford experiment. This is **minimax optimality up to constants** within the stated measurement model.

The three terms in the rate have distinct roles. The constant term accounts for bounded loss. The spectral-decay term balances an approximation error of order $Ls^{1-\alpha}$ against an estimation error of order $s\sqrt{d/T}$. The term $\sqrt{d^3/T}$ is the full-dimensional rate, obtained by retaining all $d$ eigenvalues. The minimum selects the strongest of these bounds. **Adaptation** means that the same reconstruction rule achieves the guarantee across all the stated spectral classes without being given $\alpha$, $L$, or the eigenbasis.

### Corollary 4: optimal rates for bounded rank

**Corollary 4.** For $\mathcal D_{d,r}=\{\rho\in\mathcal D_d:\mathrm{rank}(\rho)\le r\}$ and $1\le r\le d$,

```math
c\min\{1,r\sqrt{d/T}\}
\le R_T^*(\mathcal D_{d,r})
\le\sup_{\rho\in\mathcal D_{d,r}}\mathbb E_\rho\|\widehat\rho-\rho\|_{\mathrm{tr}}
\le\min\{2,Cr\sqrt{d/T}\}.
```

The constants are universal and positive. This holds for both OMD and weighted PLS under their stated fitting conditions.

The class $\mathcal D_{d,r}$ consists of states with at most $r$ nonzero eigenvalues. For these states, $\tau_r(\rho)=0$, and the rate reduces to $r\sqrt{d/T}$ until the constant loss bound becomes active. For pure states ($r=1$), it is $\sqrt{d/T}$; for the unrestricted rank bound $r=d$, it is $\sqrt{d^3/T}$. The estimator does not need to know $r$. In the regime of small target error $\varepsilon$, the matching bounds give a required number of copies of order $dr^2/\varepsilon^2$, up to universal constants.

### Lean declarations

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
