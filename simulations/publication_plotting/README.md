# Publication figure rendering

Run `python3 REPRODUCE_FIGURES.py` to regenerate all four simulation figures
from the included summary tables. The tables were compared with MSI by SHA-256.
This step is not a fresh statistical experiment or a raw-data validator.

`plot_main_figures.py` preserves the original axis geometry while removing
subtitle/footer material supplied in the manuscript captions. Against the
accepted publication SVGs, all twelve plotted curve paths match exactly.
`plot_block_figure.py` uses the final block summary with the common spectral
global endpoint. `plot_supplement_comparison.py` plots only the paper-tolerance
profiles. Both supplement PNGs matched the accepted exports pixel-for-pixel
under the tested Matplotlib 3.9.4 environment.

The original MSI script `three_estimator_comparison_2026-09-11/plot_selected.py`
also draws a historical block panel; that panel is superseded by the global
rerun and is not the block panel in the current manuscript. Use the publication
renderer here for the current four figures.
