#!/usr/bin/env python3
"""Reproduce the C proof programs and opcode metadata from a THTH checkout.

This translates the deliberately small, straight-line proof-construction language
used by the upstream builtins. Every generated step calls the checked C kernel;
no theorem or resulting judgement is imported as a trusted fact.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def clean(s):
    return re.sub(r"//[^\n]*", "", s)

def split(s, sep=','):
    depth = 0
    quoted = False
    start = 0
    out = []
    for i, c in enumerate(s):
        if c == '"' and (i == 0 or s[i-1] != '\\'):
            quoted = not quoted
        if quoted:
            continue
        if c in '([{': depth += 1
        if c in ')]}': depth -= 1
        if c == sep and depth == 0:
            out.append(s[start:i].strip())
            start = i+1
    if s[start:].strip(): out.append(s[start:].strip())
    return out

def close(s, start, left='{', right='}'):
    depth = 1
    i = start+1
    while depth:
        if s[i] == left: depth += 1
        if s[i] == right: depth -= 1
        i += 1
    return i

def metadata(up):
    labels = re.findall(r'^\s*(\w+)\s*=\s*(\d+),', clean((up/'src/opcodes/opcode_labels.rs').read_text()), re.M)
    enum = '\n'.join(f'    TT_{name} = {num},' for name,num in labels)
    (ROOT/'include/tt_opcodes.h').write_text('/* Generated from upstream opcode_labels.rs. */\n#ifndef TT_OPCODES_H\n#define TT_OPCODES_H\ntypedef enum {\n'+enum+'\n} tt_opcode;\n#endif\n')
    entries=[]
    for p in sorted((up/'src/opcodes').glob('*/*.rs')):
        s=clean(p.read_text())
        if 'OpcodeMetadata {' not in s: continue
        name=re.search(r'opcode_label: OpcodeLabel::(\w+)',s)[1]
        nj=int(re.search(r'judgements_dependencies:\s*(\d+)',s)[1])
        nc=re.search(r'context_dependency:\s*(true|false)',s)[1]=='true'
        output=re.search(r'output_type: OpcodeOutputType::(\w+)',s)[1]=='Context'
        masks=[]
        for body in re.findall(r'ContextAllowedDependencies\s*\{(.*?)\}',s,re.S):
            pair=[]
            for k in ['judgement_refs','free_context_refs']:
                m=re.search(k+r':\s*FxHashSet::from_iter\(\[(.*?)\]\)',body,re.S)
                pair.append(sum(1<<int(x) for x in re.findall(r'\d+',m[1])) if m else 0)
            masks.append(pair)
        entries.append(dict(name=name,nj=nj,nc=int(nc),out=int(output),masks=masks))
    lines=[]
    for e in entries:
        j=','.join(str(x[0]) for x in e['masks']) or '0'
        f=','.join(str(x[1]) for x in e['masks']) or '0'
        lines.append(f'    [TT_{e["name"]}] = {{"{e["name"]}", {e["nj"]}, {e["nc"]}, {len(e["masks"])}, {e["out"]}, {{{j}}}, {{{f}}}}},')
    (ROOT/'src/kernel/metadata.inc').write_text('/* Generated; see tools/port_proofs.py. */\n'+ '\n'.join(lines)+'\n')
    return entries

class Translator:
    def __init__(self, functions):
        self.functions=functions
        self.ops={}
        self.serial=0
        self.vars=set()

    def value(self,s):
        s=s.strip()
        s=re.sub(r'&(?:mut\s+)?','',s)
        s=s.replace('.hash','').replace('.clone()','')
        s=s.replace('Default::default()','0').replace('None','0')
        s=re.sub(r'Some\((.*?)\)',r'\1',s)
        s=re.sub(r'\b(type_var_contexts|u0_var_contexts|type_vars|type_variables)\[',r'\1.v[',s)
        return s

    def expression(self,s):
        s=s.strip()
        v=self.value(s)
        m=re.fullmatch(r'create_variables_from_context\([^,]+,\s*\[(\w+)\]\)\[0\]',v)
        if m:return f'proof_variable(e, {m[1]})'
        m=re.fullmatch(r'define_u0_type_variable_contexts\([^,]+,\s*(\w+),\s*(\d+)\)',v)
        if m:return f'proof_type_contexts(e, {m[1]}, {m[2]})'
        m=re.fullmatch(r'create_variables_from_context\([^,]+,\s*(\w+)\)',v)
        if m:return f'proof_variables(e, {m[1]})'
        if v in ('define_u_0(graph_store)','define_u_0(graph_store)'):
            return 'p_define_u0(e)'
        m=re.fullmatch(r'(\w+)\s*\.\s*apply_for_(?:judgement|context_fragment)_or_panic\s*\((.*)\)',s,re.S)
        if m:
            args=split(m[2]); assert len(args)==4,args
            js=self.value(args[1]); fs=self.value(args[3])
            js=js[1:-1] if js.startswith('[') else ''
            fs=fs[1:-1] if fs.startswith('[') else ''
            jlist=split(js); flist=split(fs)
            return f'proof_step(e, TT_{self.ops[m[1]]}, (tt_id[]){{{js or "0"}}}, {len(jlist)}, {self.value(args[2])}, (tt_id[]){{{fs or "0"}}}, {len(flist)}, __FILE__, __LINE__)'
        m=re.fullmatch(r'(\w+)\s*\((.*)\)',s,re.S)
        if m and m[1] in self.functions:
            args=split(m[2])[1:]
            return f'p_{m[1]}(e'+''.join(', '+self.value(a) for a in args)+')'
        return self.value(s)

    def block(self,s,returns=False):
        out=[]
        while s.strip():
            s=s.lstrip()
            if s.startswith('for '):
                m=re.match(r'for (\w+) in (\d+)\.\.(\d+)\s*\{',s); assert m,s[:200]
                end=close(s,m.end()-1)
                self.serial+=1
                var=m[1] if m[1]!='_' else f'loop_{self.serial}'
                out.append(f'for (unsigned {var}={m[2]}; {var}<{m[3]}; ++{var}) {{\n'+self.block(s[m.end():end-1])+'\n}')
                s=s[end:];continue
            if s.startswith('if '):
                m=re.match(r'if (\w+\s*<\s*\d+)\s*\{',s); assert m,s[:200]
                end=close(s,m.end()-1)
                out.append(f'if ({m[1]}) {{\n'+self.block(s[m.end():end-1])+'\n}')
                s=s[end:];continue
            parts=split(s,';')
            stmt=parts[0]
            s=s[len(stmt):].lstrip(';')
            if stmt.startswith('graph_store.save_'): continue
            m=re.fullmatch(r'let\s+(?:mut\s+)?(\w+)\s*=\s*(\w+)\s*\{\s*\}',stmt,re.S)
            if m: self.ops[m[1]]=m[2];continue
            m=re.fullmatch(r'let\s+(?:mut\s+)?(.+?)\s*=\s*(.*)',stmt,re.S)
            if m:
                lhs,rhs=m.groups()
                val=self.expression(rhs)
                if lhs.startswith('('):
                    self.serial+=1
                    tmp=f'tuple_{self.serial}'
                    out.append(f'proof_tuple {tmp} = {val};')
                    for i,v in enumerate(split(lhs[1:-1])):
                        if v=='_':continue
                        out.append(f'tt_id {v} = {tmp}.v[{i}];')
                        self.vars.add(v)
                else:
                    typ='proof_tuple ' if val.startswith(('proof_type_contexts(', 'proof_variables(')) else 'tt_id '
                    decl='' if lhs in self.vars else typ
                    self.vars.add(lhs)
                    out.append(f'{decl}{lhs} = {val};')
                continue
            m=re.match(r'(\w+)\s*=\s*(.*)',stmt,re.S)
            if m:
                out.append(f'{m[1]} = {self.expression(m[2])};');continue
            if returns and not s.strip():
                if stmt.startswith('('):
                    out.append('return (proof_tuple){{'+', '.join(self.value(x) for x in split(stmt[1:-1]))+'}};')
                else: out.append('return '+self.expression(stmt)+';')
            else: raise ValueError('Unsupported proof statement: '+stmt[:300])
        # Rust underscore-prefixed bindings deliberately retain proof steps
        # whose outputs are unused. Mark the C values consumed without removing
        # those checked calls or suppressing diagnostics for generated code.
        marked=[]
        for line in out:
            marked.append(line)
            unused=re.match(r'tt_id (_\w+)\s*=',line)
            if unused:
                marked.append(f'(void){unused[1]};')
        return '\n'.join('    '+line for line in marked)

def proofs(up):
    functions={}
    sources={}
    paths=sorted((up/'src/builtins').glob('*.rs'))
    paths.append(up/'tests/no_driver/manual_library/pr.rs')
    for p in paths:
        if p.name in ('mod.rs','create_builtins_vector.rs'): continue
        original=p.read_text();s=clean(original)
        for m in re.finditer(r'pub fn (\w+)\s*\((.*?)\)\s*->\s*(.*?)\{',s,re.S):
            end=close(s,m.end()-1)
            functions[m[1]]=(m[2],m[3].strip(),s[m.end():end-1])
            sources[str(p.relative_to(up))]=hashlib.sha256(original.encode()).hexdigest()
    for stem,prop,proof in [('comp','comp_signature_u0_judgement','comp_proof'),('product_commutes','proposition','product_switch_proof')]:
        p=up/f'tests/no_driver/{stem}.rs'
        original=p.read_text();s=clean(original)
        m=re.search(r'fn test_\w+\(\)\s*\{',s)
        body=s[m.end():close(s,m.end()-1)-1]
        body=re.sub(r'let mut graph_store = SimpleGraphStore::new\(\);','',body)
        body=body[:body.index('if !verify(')]+f'({prop}, {proof})'
        functions['test_'+stem]=('', '(Judgement, Judgement)', body)
        sources[str(p.relative_to(up))]=hashlib.sha256(original.encode()).hexdigest()
    decls=[];bodies=[]
    for name,(args,ret,body) in functions.items():
        params=split(args)
        tail=''.join(', tt_id '+a.split(':')[0].strip() for a in params[1:])
        typ='proof_tuple' if ret.startswith('(') else 'tt_id'
        sig=f'{typ} p_{name}(tt_engine *e{tail})'
        decls.append(sig+';')
        t=Translator(functions)
        # The test projection helper uses the same universe/context helpers as
        # the hand-ported theorem tests; translate those simple bindings here.
        bodies.append(sig+' {\n'+t.block(body,True)+'\n}')
    (ROOT/'src/proofs_generated.inc').write_text('/* Generated from THTH proof construction programs. Do not edit. */\n'+ '\n'.join(decls)+'\n\n'+'\n\n'.join(bodies)+'\n')
    (ROOT/'docs/proof_sources.json').write_text(json.dumps(sources,indent=2)+'\n')
    return len(functions)

def main():
    p=argparse.ArgumentParser();p.add_argument('upstream',type=Path)
    a=p.parse_args();up=a.upstream/'rust_backend'
    entries=metadata(up)
    print(f'Generated metadata for {len(entries)} opcodes')
    print(f'Generated {proofs(up)} proof functions')

if __name__=='__main__':main()
