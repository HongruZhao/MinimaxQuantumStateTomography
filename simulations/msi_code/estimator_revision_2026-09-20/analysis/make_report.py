"""Build the final, evidence-linked PDF only from complete validated runs."""
import json
from pathlib import Path
from xml.sax.saxutils import escape
import matplotlib
from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, Image, PageBreak

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'output/pdf'
OUT.mkdir(parents=True, exist_ok=True)
font_dir = Path(matplotlib.get_data_path()) / 'fonts/ttf'
pdfmetrics.registerFont(TTFont('AuditSans', str(font_dir/'DejaVuSans.ttf')))
pdfmetrics.registerFont(TTFont('AuditSansBold', str(font_dir/'DejaVuSans-Bold.ttf')))
pdfmetrics.registerFontFamily('AuditSans', normal='AuditSans', bold='AuditSansBold', italic='AuditSans', boldItalic='AuditSansBold')
styles = getSampleStyleSheet()
styles.add(ParagraphStyle(name='AuditTitle', fontName='AuditSansBold', fontSize=20, leading=25, textColor=colors.HexColor('#183A52'), spaceAfter=12))
styles.add(ParagraphStyle(name='AuditHeading', fontName='AuditSansBold', fontSize=13, leading=17, textColor=colors.HexColor('#183A52'), spaceBefore=8, spaceAfter=8))
styles.add(ParagraphStyle(name='AuditBody', fontName='AuditSans', fontSize=9.3, leading=14, spaceAfter=8))
styles.add(ParagraphStyle(name='AuditSmall', fontName='AuditSans', fontSize=8, leading=11, spaceAfter=6))
styles.add(ParagraphStyle(name='AuditCell', fontName='AuditSans', fontSize=8.2, leading=11))


def paragraph(text, style='AuditBody'):
    return Paragraph(text.replace('\u2013','-').replace('\u2014','-').replace('\u2011','-'), styles[style])


def table(rows, widths):
    cells = [[paragraph(escape(str(x)), 'AuditCell') for x in row] for row in rows]
    t = Table(cells, colWidths=widths, repeatRows=1, hAlign='LEFT')
    t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#E8EEF3')),
                          ('VALIGN',(0,0),(-1,-1),'TOP'),('LINEBELOW',(0,0),(-1,0),.7,colors.HexColor('#8194A4')),
                          ('BOTTOMPADDING',(0,0),(-1,-1),6),('TOPPADDING',(0,0),(-1,-1),6),
                          ('ROWBACKGROUNDS',(0,1),(-1,-1),[colors.white,colors.HexColor('#F7F9FB')])]))
    return t


def image(name, width=505):
    from PIL import Image as PILImage
    path=ROOT/'figures'/name
    with PILImage.open(path) as pic:
        w,h=pic.size
    return Image(str(path), width=width, height=width*h/w)


def page(canvas, doc):
    canvas.setFont('AuditSans',8)
    canvas.setFillColor(colors.HexColor('#667788'))
    canvas.drawString(44,25,'Shadow Tomography | MSI estimator audit | 20 September 2026')
    canvas.drawRightString(A4[0]-44,25,str(doc.page))


global_result=json.loads((ROOT/'reports/global_summary.json').read_text())
small=json.loads((ROOT/'reports/convergence_n4_summary.json').read_text())
large=json.loads((ROOT/'reports/convergence_n8_summary.json').read_text())
audit=json.loads((ROOT/'reports/msi_solver_audit.json').read_text())
for x in [global_result,small,large]:
    assert x['status']=='complete'
assert audit['status']=='passed'
assert global_result['max_pairwise_output_difference']==0
total=small['checked_fits']+large['checked_fits']
story=[]
story.append(paragraph('Estimator audit and convergence', 'AuditTitle'))
story.append(paragraph('<b>The global edge-case mismatch is fixed.</b> When k=n, all three labels now run the same fresh spectral reconstruction specified in Supplement S.7.6. MW-PLS no longer runs Frank-Wolfe at this endpoint.'))
story.append(paragraph('The former generic MW implementation had the correct quadratic objective but did not use the paper’s prescribed common selection. At k&lt;n, the three objectives differ, so equal runtimes or equal estimates are not required.'))
story.append(paragraph('Global rerun: 100 original datasets', 'AuditHeading'))
rows=[['Method','Mean trace-norm error','Median solver time','Time IQR']]
for r in global_result['rows']:
    rows.append([r['method'],f"{r['trace_norm_error']:.10f}",f"{1000*r['median_seconds']:.2f} ms",f"{1000*r['seconds_q25']:.2f}–{1000*r['seconds_q75']:.2f} ms"])
story.append(table(rows,[72,156,123,156]))
story.append(Spacer(1,10))
story.append(paragraph('n=k=8, d=256, T=16,384. Input hashes match the original benchmark. Every dataset returned identical matrices under all three labels: maximum pairwise difference 0. Each label had one discarded warm-up and three fresh timed solves. Timings were measured independently.'))
story.append(image('vary_block_size_three_corrected.png'))
story.append(paragraph('The k&lt;n points above retain the original benchmark data. Only the global endpoint was rerun. The old generic global MW median was 0.965 seconds; the corrected shared routine takes about 0.022 seconds. Theoretical statements and Lean sources were not changed.', 'AuditSmall'))
story.append(PageBreak())

story.append(paragraph('Increasing T at d=16', 'AuditTitle'))
story.append(paragraph('20 independent datasets per state and design; T=256, 1,024, 4,096, 16,384, 65,536, 262,144, 1,048,576, 4,194,304. All three methods receive the same nested empirical means. Bands are pointwise 95% bootstrap intervals for mean trace-norm loss.'))
story.append(image('convergence_n4_log.png'))
story.append(paragraph('Mean errors at T=4,194,304', 'AuditHeading'))
rows=[['Design / state','PLS','OMD','MW-PLS']]
family_names={'rank8_diagonal':'Rank 8, diagonal','rank8_rotated':'Rank 8, rotated','polynomial_rotated':'Polynomial, rotated'}
for k in [2,4]:
    for family,name in family_names.items():
        cells=[r for r in small['rows'] if r['k']==k and r['family']==family and r['T']==4194304]
        vals={r['method']:r['trace_norm_error'] for r in cells}
        rows.append([('Periodic / ' if k==2 else 'Global / ')+name,*[f'{vals[m]:.5f}' for m in ['PLS','OMD','MW-PLS']]])
story.append(table(rows,[267,80,80,80]))
story.append(Spacer(1,8))
story.append(paragraph('The rotated states use a fixed Haar-drawn eigenbasis. Polynomial eigenvalues are proportional to j^-2. Solvers receive neither these structural choices nor the true state. At the global design, all three curves coincide because the returned matrices coincide.'))
story.append(PageBreak())

story.append(paragraph('Extending the paper’s d=256 example', 'AuditTitle'))
story.append(paragraph('10 new independent datasets, k=2, rank-eight diagonal state. The upper T value is 16 times the original paper’s maximum. Error and optimization accuracy are checked separately.'))
story.append(image('convergence_n8.png'))
rows=[['Copies T','PLS error','OMD error','MW-PLS error']]
for T in [1024,262144,4194304]:
    values={r['method']:r['trace_norm_error'] for r in large['rows'] if r['T']==T}
    rows.append([f'{T:,}',*[f'{values[m]:.5f}' for m in ['PLS','OMD','MW-PLS']]])
story.append(table(rows,[126,127,127,127]))
story.append(Spacer(1,8))
story.append(image('stopping_checks.png',width=440))
story.append(paragraph(f'All {total:,} production convergence fits passed independent full-spectrum checks. OMD requires both its original and regularized gaps to pass; MW uses its recomputed first-order gap. PLS is checked against a full spectral projection. The plots use raw means without forced monotonicity.', 'AuditSmall'))
story.append(PageBreak())

story.append(paragraph('What was checked', 'AuditTitle'))
story.append(paragraph(f'The local and MSI audits each passed {len(audit["checks"])} checks. Additional checks at n=8 compared 64 structured/random Pauli labels for each k=2,4,8 against independent label propagation; maximum disagreement was below 4×10^-17.'))
rows=[['Paper object','Implementation / independent check'],
      ['PLS, equation (14)','Inverse measurement channel, then density-matrix projection; full-spectrum projection agreement.'],
      ['OMD, equations (16)–(17)','ADMM equations in S.7; original and regularized primal-dual gaps recomputed from saved dual witnesses. Independent PDHG reference.'],
      ['MW-PLS, equations (18)–(20)','Q=1/2 <sigma,L(sigma)>-<Y,sigma>; gradient L(sigma)-Y; exact quadratic line search and full-gradient gap. Independent APG reference.'],
      ['Global common selection, S.7.6','Same spectral routine for every label; exact finite-data output equality in all 100 original datasets.'],
      ['Measurement channel','Transfer formula compared to explicit Pauli-label propagation, direct Kronecker Pauli expansion, inversion, and score identity.']]
story.append(table(rows,[150,357]))
story.append(Spacer(1,10))
story.append(paragraph('Why the limiting error is zero', 'AuditHeading'))
story.append(paragraph('At a fixed dimension, the empirical projector mean converges to M(rho), and the positive channel multipliers make M and L invertible. PLS follows by continuity of the inverse channel and nonexpansiveness of projection. For OMD, the forward discrepancy is at most twice the sampling error plus its vanishing objective tolerance. For MW-PLS, positive curvature and its vanishing first-order gap force the state error to vanish. Trace-norm loss is bounded by two, so expected loss also tends to zero.'))
story.append(paragraph('The complete elementary argument is in reports/FIXED_DIMENSION_CONSISTENCY.md. It applies to accepted fits; a failed iteration/time cap is not a valid estimator certificate. Finite simulations provide supporting evidence, not a proof of the infinite-T limit or uniform minimax performance.'))
story.append(paragraph('Evidence and reproduction', 'AuditHeading'))
story.append(paragraph('Source: src/estimators.py, src/global_solution.py, src/solvers.py, src/omd_tolerance.py. Protocol: PROTOCOL.md. Machine-readable summaries and audit receipts: reports/. Raw empirical means, estimates, dual witnesses, and solver histories: results/. Run configurations: configs/. MSI submission scripts: jobs/.', 'AuditSmall'))
story.append(paragraph('MSI revision: /projects/standard/galin/shared/hongru/Clifford_Minimax/estimator_revision_2026-09-20. Original datasets and source snapshots are preserved. Numerical gaps are floating-point diagnostics, not interval-arithmetic or Lean proofs. The experiments use the paper’s statistical tolerances; the extended sweep permits larger iteration caps, stated in PROTOCOL.md.', 'AuditSmall'))
story.append(paragraph('Primary algorithm reference: M. Jaggi, “Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization,” ICML 2013, <link href="https://proceedings.mlr.press/v28/jaggi13.html" color="#1769AA">proceedings.mlr.press/v28/jaggi13.html</link>. The precise tomography objectives and global selection are taken from the current manuscript and supplement.', 'AuditSmall'))
doc=SimpleDocTemplate(str(OUT/'MSI_ESTIMATOR_AUDIT_AND_CONVERGENCE.pdf'),pagesize=A4,
                      rightMargin=44,leftMargin=44,topMargin=42,bottomMargin=42,
                      title='MSI estimator audit and convergence',author='Shadow Tomography research project')
doc.build(story,onFirstPage=page,onLaterPages=page)
print(OUT/'MSI_ESTIMATOR_AUDIT_AND_CONVERGENCE.pdf')
