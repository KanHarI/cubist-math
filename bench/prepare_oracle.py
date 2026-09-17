#!/usr/bin/env python3
"""Generate a Rust trace replay executable beside a prepared baseline."""
import argparse
import re
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('baseline',type=Path);a=p.parse_args()
root=Path(__file__).resolve().parents[1]
labels=re.findall(r'TT_(\w+) = (\d+)',(root/'include/tt_opcodes.h').read_text())
arms='\n'.join(f'        {v} => {name}{{}}.into(),' for name,v in labels if name not in ('None', 'Nop', 'SuspForm', 'SuspNorth', 'SuspSouth', 'SuspMerid', 'SuspElim', 'SuspMeridComp', 'Transport', 'Apd'))
source=re.sub(r'//[^\n]*','',(a.baseline/'src/ast/exp.rs').read_text())
variants=[]
for m in re.finditer(r'^    (\w+)(?:\s*\{(.*?)\})?\s*,',source,re.M|re.S):
    name,fields=m.groups()
    field_names=re.findall(r'(\w+)\s*:',fields or '')
    variants.append((name,field_names))
node_order=['Axiom','CRef','UCRef','VRef','DRef','U','UUOmega','UUKappa','Void','Unit','Singleton','Nat','ZN','SN','Lambda','Ap','Pi','Sigma','Tuple','Sum','Eq','Inl','Inr','Refl','DefEq','W','WSup','IndNat','IndSigma','IndSum','IndEq','IndVoid','IndUnit','IndW','Temp']
fingerprints=[]
contains_w=[]
for name,fields in variants:
    kind=node_order.index(name)+1
    param='0u64';children=[]
    if fields==['judgement_hash']:param='*jm.get(judgement_hash).expect("unknown judgement ref") as u64'
    elif fields==['context_hash']:param='*cm.get(context_hash).expect("unknown context ref") as u64'
    elif fields==['i']:param='*i as u32 as u64'
    else:children=fields
    pattern=f'ExpAst::{name}'+(' { '+', '.join(fields)+' }' if fields else '')
    condition='true' if name=='IndW' else ' || '.join(f'contains_ind_w({c})' for c in children) or 'false'
    contains_w.append(f'        {pattern} => {condition},')
    body=f'let mut h = mix({kind}u64 + (({param}) << 32));'
    body+=''.join(f' h = mix(h ^ fp({c},jm,cm));' for c in children)
    fingerprints.append(f'        {pattern} => {{ {body} h }},')
template=(Path(__file__).with_name('rust_oracle.rs')).read_text()
template=template.replace('/* OPCODE_ARMS */',arms).replace('/* FINGERPRINT_ARMS */','\n'.join(fingerprints))
template=template.replace('/* CONTAINS_W_ARMS */','\n'.join(contains_w))
(a.baseline/'src/bin/oracle.rs').write_text(template)
