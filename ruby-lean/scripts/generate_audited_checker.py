#!/usr/bin/env python3
"""Generate the trace-indexed checker from its single raw source implementation.

The generated code is checked by Lean; the bridge independently checks every
constructor against the real registry. --check rejects stale generated sources.
"""
from pathlib import Path
import argparse
import re

ROOT = Path(__file__).resolve().parents[1]
MODULES = ['CheckInit', 'MethodCertificate', 'MethodFlowCertificate', 'BodyCache',
           'ReceiverCache', 'SingletonCache', 'Certified', 'CheckCallbackBody',
           'CallbackCache', 'CheckMethodFlow', 'BoundCallbackCache', 'FlowCheck', 'Raw']
FAMILIES = r'(?:DJudge(?:All|Seq|Pairs|RecAll|Rec)?|InitJudge(?:Seq|All)?|DFlow(?:Seq|All)?|DMethod(?:FlowSeq|Flow|Seq|All)?)'

def generate(module):
    source = ROOT / 'Ratchet/Check' / f'{module}.lean'
    text = source.read_text()
    for item in MODULES:
        text = text.replace(f'import Ratchet.Check.{item}\n', f'import Ratchet.Audit.{item}\n')
    text = text.replace('namespace Ratchet\n', 'namespace Ratchet.Audit\nopen Ratchet\n')
    text = text.replace('end Ratchet\n', 'end Ratchet.Audit\n')
    # Every judgment field has a computational trace constrained by its proof's
    # index. Constructor notation infers that trace from the selected rules.
    lines = text.splitlines(keepends=True)
    out = []
    in_judged = False
    for line in lines:
        if line.startswith('  judged :'):
            out.append('  {rulesUsed : List String}\n')
            in_judged = True
        elif line and not line[0].isspace():
            in_judged = False
        elif re.match(r'  \w+\s*:', line):
            in_judged = False
        if in_judged:
            line = re.sub(rf'\b({FAMILIES})\b', r'\1 (used := rulesUsed)', line)
        if 'ordinary : Option (PLift (' in line:
            line = line.replace('PLift (', 'TraceLift (fun used => ')
            line = re.sub(rf'\b({FAMILIES})\b', r'\1 (used := used)', line)
        out.append(line)
    text = ''.join(out).replace('PLift.up', 'TraceLift.up')
    if module == 'CheckInit':
        text = text.replace('let finish (hj : InitJudge ', 'let finish {used : List String} (hj : InitJudge (used := used) ')
        text = text.replace('finish (by simpa only [hctx, hr]', 'finish (used := c.rulesUsed) (by simpa only [hctx, hr]')
        text = text.replace('finish (by simpa only [hctx, ha]', 'finish (used := "InitJudge.ignoreResult" :: (c.rulesUsed ++ [])) (by simpa only [hctx, ha]')
    if module == 'CheckMethodFlow':
        text = text.replace('cases he', 'simp only [he]')
    if module == 'Raw':
        text = text.replace(".if' hc ht (by", ".if' (used_0 := DJudge.rules hc) (used_1 := DJudge.rules ht) (used_2 := DJudge.rules he) hc ht (by")
        text = text.replace('.ifNoElse hc (by', '.ifNoElse (used_0 := DJudge.rules hc) (used_1 := DJudge.rules ht) hc (by')
        text = text.replace('.ifTruthy hx hf ha ht (by', '.ifTruthy (used_0 := DJudge.rules ht) (used_1 := DJudge.rules he) hx hf ha ht (by')
        text = text.replace('.ifTruthyNoElse hx hf ha (by', '.ifTruthyNoElse (used_0 := DJudge.rules ht) hx hf ha (by')
        text = text.replace('.defDeclOpt (d := decl) (σ := o.2) (Γb := Γb) hshape', '.defDeclOpt (d := decl) (σ := o.2) (Γb := Γb) (used_0 := DJudge.rules hd) (used_1 := DJudge.rules hbj) hshape')
        text = text.replace('DJudge.callSigOpt (σ := o.2) (Γb := Γb) hshape', 'DJudge.callSigOpt (σ := o.2) (Γb := Γb) (used_0 := DJudge.rules hd) (used_1 := DJudge.rules hbj) hshape')
        text = text.replace(".while' (by subst", ".while' (used_0 := DJudge.rules hc) (used_1 := DJudge.rules hb) (by subst")
        text = text.replace('.ifIsAIvar hx hg (by rw [hi₁] at ht; exact ht)', '.ifIsAIvar (used_0 := DJudge.rules ht) (used_1 := DJudge.rules he) hx hg (by simpa only [DJudge.rules, hi₁] using ht)')
        text = text.replace('(by rw [hi₂] at he; cases hctx; exact he)', '(by simpa only [DJudge.rules, hctx, hi₂] using he)')
        text = text.replace('.ifCaseEq ht (hρ ▸ hx) hg hf hth (by', '.ifCaseEq (used_0 := DJudge.rules hth) (used_1 := DJudge.rules he) ht (hρ ▸ hx) hg hf hth (by')
        text = text.replace('.sendUnion hx ha₁ ha₂ hl (by', '.sendUnion (used_0 := DJudge.rules hl) (used_1 := DJudge.rules hr) hx ha₁ ha₂ hl (by')
        text = text.replace('by cases hctx; cases hi; exact hr', 'by simpa only [DJudge.rules, hctx, hi] using hr')
        text = text.replace('.ifIsA hx hg ht (by', '.ifIsA (used_0 := DJudge.rules ht) (used_1 := DJudge.rules he) hx hg ht (by')
        text = text.replace('.ifNilQuery hx hg ht (by', '.ifNilQuery (used_0 := DJudge.rules ht) (used_1 := DJudge.rules he) hx hg ht (by')
        text = text.replace('by cases hctx; cases hi; exact he', 'by simpa only [DJudge.rules, hctx, hi] using he')
        text = text.replace('by cases hctx; cases hi; exact ht', 'by simpa only [DJudge.rules, hctx, hi] using ht')
    if module == 'MethodCertificate':
        text = text.replace('def CertifiedMethod.ofOrdinary ', 'def CertifiedMethod.ofOrdinary {used : List String} ')
        text = text.replace('(h : ∀ code, DJudge ', '(h : ∀ code, DJudge (used := used) ')
    if module == 'ReceiverCache':
        text = text.replace('theorem CallableMemberAt.own_judged ', 'theorem CallableMemberAt.own_judged {used : List String} ')
        text = text.replace('(hb : DJudge ', '(hb : DJudge (used := used) ')
        text = text.replace('    DJudge b.body.params', '    DJudge (used := used) b.body.params')
    return (f'-- Generated from Ratchet/Check/{module}.lean by scripts/generate_audited_checker.py.\n'
            '-- Edit the raw source and regenerate; Lean checks the indexed proof and trace.\n'
            'import Ratchet.Audit.Erase\n' + text)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    stale = []
    for module in MODULES:
        path = ROOT / 'Ratchet/Audit' / f'{module}.lean'
        expected = generate(module)
        if args.check:
            if not path.exists() or path.read_text() != expected:
                stale.append(str(path.relative_to(ROOT)))
        else:
            path.write_text(expected)
    if stale:
        parser.error('stale audited checker modules: ' + ', '.join(stale))

if __name__ == '__main__':
    main()
