"""Render a concise report from the checked numerical records."""
from pathlib import Path
import json

from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import inch
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, Image, PageBreak

ROOT=Path(__file__).resolve().parent.parent


def main():
    fresh=json.loads((ROOT/'reports/fresh_review_validation.json').read_text())
    legacy=json.loads((ROOT/'reports/legacy_revalidation.json').read_text())
    tests=json.loads((ROOT/'reports/review_regressions.json').read_text())
    assert fresh['status']==legacy['status']==tests['status']=='passed'
    styles=getSampleStyleSheet()
    styles.add(ParagraphStyle(name='BodyReview',fontName='Helvetica',fontSize=10.1,leading=14,spaceAfter=8))
    styles.add(ParagraphStyle(name='SmallReview',fontName='Helvetica',fontSize=8.8,leading=12,spaceAfter=6))
    styles.add(ParagraphStyle(name='TableReview',fontName='Helvetica',fontSize=9.2,leading=12))
    styles.add(ParagraphStyle(name='ReviewTitle',fontName='Helvetica-Bold',fontSize=21,leading=25,textColor=colors.HexColor('#193e5b'),spaceAfter=10))
    def p(s,style='BodyReview'):return Paragraph(s,styles[style])
    def table(rows,widths):
        t=Table([[p(str(x),'TableReview') for x in row] for row in rows],colWidths=widths,hAlign='LEFT')
        t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#eaf0f4')),
            ('VALIGN',(0,0),(-1,-1),'TOP'),('LEFTPADDING',(0,0),(-1,-1),7),
            ('RIGHTPADDING',(0,0),(-1,-1),7),('TOPPADDING',(0,0),(-1,-1),7),
            ('BOTTOMPADDING',(0,0),(-1,-1),7),('LINEBELOW',(0,0),(-1,0),.6,colors.HexColor('#8ea7b8')),
            ('LINEBELOW',(0,-1),(-1,-1),.5,colors.HexColor('#bbc9d3'))]))
        return t
    story=[p('Solver review: corrections and fresh tests','ReviewTitle'),
        p('Shadow Tomography | 20 September 2026 | corrected MSI revision','SmallReview'),
        p('<b>The review found three real implementation defects.</b> They are corrected. '
          'The PLS and MW-PLS objectives remain unchanged; the default OMD numerical updates also remain unchanged.'),
        table([['Confirmed defect','Correction'],
          ['OMD at tighter accuracy','The requested original-objective tolerance now determines the regularization: eta = 0.005 times that tolerance. Both original and regularized gaps must pass.'],
          ['Validation trusted solver limits','The validator independently computes limits from d, T and the requested accuracy, recomputes gaps from saved matrices and dual witnesses, and rejects inconsistent metadata.'],
          ['Stale results could be reused','Reuse now requires matching sources, configuration, input hashes and output hashes. A mismatch raises an error; the old result is preserved.']], [132,390]),
        Spacer(1,12),p('<b>Reproduced failure, then corrected it</b>'),
        p('On the stored d = 16, k = 2, T = 256 input, the requested original gap was 2.5 x 10<super>-7</super>.'),
        table([['','Before correction','After correction'],
               ['Regularization eta','1.25 x 10<super>-3</super>','1.25 x 10<super>-9</super>'],
               ['Iterations','10,000 (cap reached)','200 (accepted)'],
               ['Original objective gap','2.2074 x 10<super>-4</super>','1.5773 x 10<super>-7</super>']], [170,176,176]),
        Spacer(1,8),p('An independent physical-Pauli calculation gives an objective improvement of '
          '4.1308 x 10<super>-7</super> over the old fit, exceeding the requested tolerance. '
          'Thus the old tight fit actually missed that accuracy, beyond merely failing a gap test.','SmallReview'),
        p('<b>Checks completed</b>'),
        p('The 36 targeted regression checks and the 32-check solver audit pass. '
          'All 3,090 saved default-tolerance fits pass a fresh mathematical recheck. '
          'This recheck uses historical arrays; it is not a fresh simulation of those datasets.'),
        p('The fresh study has 15 datasets and 240 final fits. All 180 fits at the paper tolerances passed immediately. '
          'One of 60 stricter OMD fits reached 20,000 iterations and was rejected. A separately recorded replay '
          'passed at 37,680 iterations without loosening its tolerance. Both attempts are retained.'),
        PageBreak(),p('Fresh simulation and what it establishes','ReviewTitle'),
        Image(str(ROOT/'figures/fresh_convergence.png'),width=522,height=522*6.2/7.4),
        Spacer(1,6)]
    rows=[['Mean trace-norm error at T = 2<super>20</super>','PLS','OMD','MW-PLS','Tight OMD']]
    names=['Periodic: rotated rank eight','Periodic: polynomial spectrum','Global: rotated rank eight']
    for case_id in range(3):
        group={r['profile']:r for r in fresh['summaries'] if r['case_id']==case_id and r['T']==1048576}
        rows.append([names[case_id]]+['%.4f'%group[label]['mean'] for label in ['PLS','OMD','MW_PLS','OMD_tight']])
    story+=[table(rows,[218,73,73,79,79]),Spacer(1,8),
       p('All three default estimators have decreasing mean errors on these finite measurement counts. '
         'For the global design, all four configurations return entrywise identical matrices. '
         'Tighter optimization need not improve statistical estimation error. These five-replication cases '
         'are numerical evidence, not a proof of an asymptotic limit, a uniform minimax claim, or formal solver correctness.','SmallReview'),
       p('Sources: reports/fresh_review_validation.json, reports/legacy_revalidation.json, '
         'reports/review_regressions.json, reports/revised_solver_audit.json. '
         'The package includes every new empirical mean, fitted state, dual witness, and both accuracy-stress attempts. '
         'Manuscript corrections are marked in blue.','SmallReview')]
    output=ROOT/'output/pdf/REVIEW_CORRECTIONS_AND_NEW_SIMULATION.pdf'
    doc=SimpleDocTemplate(str(output),pagesize=(612,792),leftMargin=45,rightMargin=45,
                          topMargin=38,bottomMargin=32,title='Solver review: corrections and fresh tests',
                          author='Shadow Tomography numerical review')
    def footer(canvas,doc):
        canvas.setFont('Helvetica',8);canvas.setFillColor(colors.HexColor('#5d6b75'))
        canvas.drawString(45,19,'MSI estimator review correction | 2026-09-20')
        canvas.drawRightString(567,19,str(doc.page))
    doc.build(story,onFirstPage=footer,onLaterPages=footer)
    print(output)


if __name__=='__main__':main()
