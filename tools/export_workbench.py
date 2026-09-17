#!/usr/bin/env python3
"""Replay every ported construction natively and emit portable, checked programs.

No judgement IDs are serialized as evidence: trace IDs become named operands.
Repeated calls are retained, including calls whose results are interned together.
The generated JSON and one-instruction-per-line .math files replay from empty.
"""
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'web/proofs'
BUILD = ROOT / 'build/workbench-export'
# Names follow the native prelude's export order. lib_ leaves demo/user names free.
GROUPS = {
    'u0': ['lib_U0'], 'unit': ['lib_Unit'], 'singleton': ['lib_singleton'],
    'void': ['lib_Void'], 'nat': ['lib_Nat', 'lib_zero'], 'uuomega': ['lib_Uomega'],
    'is_trunc': ['lib_IsTrunc'], 'is_set': ['lib_IsSet'],
    'propositional_truncation': ['lib_Trunc', 'lib_trunc_intro', 'lib_trunc_is_trunc', 'lib_trunc_elim'],
    'lem': ['LEM'], 'aoc': ['AOC'], 'pr': ['lib_pr1', 'lib_pr2'],
    'homotopy': ['lib_Homotopy', 'lib_happly', 'lib_ap', 'lib_id', 'lib_isEquiv',
                 'lib_funext', 'lib_funext_compute', 'lib_funext_unique', 'lib_id_isEquiv',
                 'lib_AreEquiv', 'lib_univalence', 'lib_transport', 'lib_ua_elim', 'lib_ua_unique'],
    'based_path_induction': ['lib_basedPathInduction'],
    'two': ['lib_Two', 'lib_zero2', 'lib_one2', 'lib_ind2', 'lib_comp2_zero', 'lib_comp2_one'],
    'unit_prop_unique': ['lib_unit_unique'], 'pi_void_unique': ['lib_pi_void_unique'],
    'wnat': ['lib_UNat', 'lib_zeroU', 'lib_succU'], 'not': ['lib_Not'],
    'is_decidable': ['lib_IsDecidable'],
    'eq_ops': ['lib_EqInv', 'lib_inv_refl', 'lib_inv_inv', 'lib_CatEq', 'lib_cat_refl'],
}
ENTRIES = {f'define_{key}': names for key, names in GROUPS.items()}
ENTRIES.update(create_pr1_pr2=['pr1', 'pr2', 'pr1_nd', 'pr2_nd'],
               test_comp=['Composition', 'composition'],
               test_product_commutes=['ProductCommutes', 'product_commutes'])


def main():
    OUT.mkdir(exist_ok=True)
    BUILD.mkdir(parents=True, exist_ok=True)
    generated = (ROOT / 'src/proofs_generated.inc').read_text()
    signatures = dict((name, typ) for typ, name in re.findall(
        r'^(tt_id|proof_tuple) p_(\w+)\([^;]+;', generated, re.M))
    assert set(signatures) == set(ENTRIES), 'Every ported routine must have an export entry'
    code = ['#include "../../src/proofs.c"', 'int main(void) {']
    entries = dict(ENTRIES, prelude_library=sum(GROUPS.values(), []))
    for key, names in entries.items():
        code += ['{', 'tt_config conf = tt_default_config();', 'conf.allow_axioms = true;',
                 'conf.max_expression_nodes = 4096;', 'tt_engine *e = tt_new(&conf);',
                 'if (!e) return 1;', f'puts("BEGIN {key}");', 'tt_set_trace(e, stdout);']
        if key == 'prelude_library':
            code += ['if (!tt_load_builtins(e, true)) return 2;',
                     'for (unsigned i = 0; i < e->nbuiltin; i++) printf("EXPORT %u\\n", e->builtin[i]);']
        else:
            extra = ', p_define_u0(e)' if key == 'create_pr1_pr2' else ''
            typ = signatures[key]
            code.append(f'{typ} result = p_{key}(e{extra});')
            for i in range(len(names)):
                value = 'result' if typ == 'tt_id' else f'result.v[{i}]'
                code.append(f'printf("EXPORT %u\\n", {value});')
            if key.startswith('test_'):
                code.append('if (!tt_verify(e, result.v[0], result.v[1])) return 3;')
        code += ['if (e->proof_failed) return 4;', 'tt_free(e);', '}']
    code += ['return 0;', '}']
    cfile = BUILD / 'export.c'
    cfile.write_text('\n'.join(code) + '\n')
    subprocess.run(['make', 'build/libthth.a'], cwd=ROOT, check=True)
    binary = BUILD / 'export'
    subprocess.run([os.environ.get('CC', 'cc'), '-O2', '-std=c11', '-Iinclude', '-Isrc',
                    str(cfile), 'build/libthth.a', '-o', str(binary)], cwd=ROOT, check=True)
    trace = subprocess.check_output([str(binary)], cwd=ROOT, text=True)
    opcodes = {int(num): name for name, num in re.findall(r'TT_(\w+) = (\d+)',
                    (ROOT / 'include/tt_opcodes.h').read_text())}
    contexts = set(re.findall(r'\[TT_(\w+)\] = \{"\w+", \d+, \d+, \d+, 1,',
                             (ROOT / 'src/kernel/metadata.inc').read_text()))
    catalogue = []
    for part in trace.split('BEGIN ')[1:]:
        key, *lines = part.strip().splitlines()
        exports = [int(line.split()[1]) for line in lines if line.startswith('EXPORT ')]
        records = [list(map(int, line.split())) for line in lines if not line.startswith('EXPORT ')]
        names = entries[key]
        assert len(exports) == len(names) and len(set(exports)) == len(exports)
        js, cs, steps, last = {}, {}, [], {}
        for i, record in enumerate(records):
            op, nj, *tail = record
            args, tail = tail[:nj], tail[nj:]
            ctx, nf, *tail = tail
            free, tail = tail[:nf], tail[nf:]
            status, result, *_ = tail
            assert status == 0, (key, i, status)
            name = f's{i + 1:04}_{opcodes[op]}'
            step = dict(name=name, op=opcodes[op], args=[js[x] for x in args],
                        context=cs[ctx] if ctx else None,
                        free=[cs[x] if x else None for x in free], hidden=False)
            steps.append(step)
            is_context = opcodes[op] in contexts
            (cs if is_context else js)[result] = name
            if not is_context:
                last[result] = name
        rename = {last[id_]: name for id_, name in zip(exports, names)}
        for step in steps:
            step['name'] = rename.get(step['name'], step['name'])
            step['args'] = [rename.get(n, n) for n in step['args']]
            if key == 'prelude_library':
                step['hidden'] = step['name'] not in names
        policy = any(step['op'] == 'Axiom' for step in steps)
        document = dict(format='thth-workbench', version=1, policy=dict(allowAxioms=policy), steps=steps)
        slug = key.removeprefix('define_').removeprefix('test_')
        title = {'prelude_library': 'Prelude library (50 exports)', 'comp': 'Function composition',
                 'product_commutes': 'Product commutativity', 'lem': 'Law of excluded middle (LEM)',
                 'aoc': 'Axiom of choice (AOC)'}.get(slug, slug.replace('_', ' ').capitalize())
        source = 'tests/no_driver/manual_library/pr.rs' if key == 'create_pr1_pr2' else (
            f'tests/no_driver/{slug}.rs' if key.startswith('test_') else f'src/builtins/{slug}.rs')
        if key == 'prelude_library': source = 'src/builtins/create_builtins_vector.rs'
        entry = dict(id=slug, title=title, file=f'{slug}.thth.json', source=source,
                     steps=len(steps), allowAxioms=policy, exports=names)
        if key.startswith('test_'): entry['verify'] = names
        catalogue.append(entry)
        (OUT / entry['file']).write_text(json.dumps(document, indent=2) + '\n')
        math = [f'# {title}', f'# Upstream: {source}', f'# Axioms: {str(policy).lower()}']
        for step in steps:
            options = []
            if step['context']: options.append('context: ' + step['context'])
            if step['free']: options.append('free: [' + ', '.join(n or '_' for n in step['free']) + ']')
            args = ', '.join(step['args']) + ('; ' + ', '.join(options) if options else '')
            math.append(f'{step["name"]} = kernel.{step["op"]}({args})')
        (OUT / f'{slug}.math').write_text('\n'.join(math) + '\n')
        if key == 'prelude_library':
            # Static module keeps browser and CLI startup independent of fetch/file APIs.
            (OUT / 'library.mjs').write_text('// Generated by tools/export_workbench.py.\nexport default ' + json.dumps(document) + ';\n')
    # Include the workbench's existing source example using the real language
    # parser, so aliases and context semantics cannot drift in a second parser.
    metadata = [dict(name=name, free=int(free)) for name, free in re.findall(
        r'\[TT_\w+\] = \{"(\w+)", \d+, \d+, (\d+),',
        (ROOT / 'src/kernel/metadata.inc').read_text())]
    identity = (ROOT / 'examples/identity.math').read_text()
    script = """import {parse} from './web/language.mjs';
import {readFileSync} from 'node:fs';
const {source, metadata} = JSON.parse(readFileSync(0, 'utf8'));
process.stdout.write(JSON.stringify(parse(source, metadata)));"""
    steps = json.loads(subprocess.check_output(['node', '--input-type=module', '-e', script],
        cwd=ROOT, input=json.dumps(dict(source=identity, metadata=metadata)), text=True))
    document = dict(format='thth-workbench', version=1, policy=dict(allowAxioms=False), steps=steps)
    (OUT / 'identity.thth.json').write_text(json.dumps(document, indent=2) + '\n')
    (OUT / 'identity.math').write_text(identity)
    catalogue.append(dict(id='identity', title='Polymorphic identity', file='identity.thth.json',
        source='examples/identity.math', steps=len(steps), allowAxioms=False,
        exports=['Identity', 'identity'], verify=['Identity', 'identity']))
    (OUT / 'catalogue.mjs').write_text('// Generated by tools/export_workbench.py.\nexport default ' + json.dumps(catalogue, indent=2) + ';\n')
    print(f'Exported {len(catalogue)} checked programs, {sum(x["steps"] for x in catalogue)} instructions')


if __name__ == '__main__':
    main()
