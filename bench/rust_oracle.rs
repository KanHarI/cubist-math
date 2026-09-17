use std::collections::{HashMap,HashSet};
use std::io::{BufRead,BufReader};
use type_theory_python_backend::ast::exp::ExpAst;
use type_theory_python_backend::drivers::{simple_graph_store::SimpleGraphStore,graph_store_trait::GraphStoreTrait};
use type_theory_python_backend::judgements::judgement::JudgementHash;
use type_theory_python_backend::context::fragment::ContextFragmentHash;
use type_theory_python_backend::opcodes::*;
use type_theory_python_backend::opcodes::opcode::{Opcode,OpcodeEnum};
use either::Either;

fn opcode(n:u32)->OpcodeEnum {match n {
/* OPCODE_ARMS */
    _=>panic!("unknown opcode {n}"),
}}
fn mix(mut x:u64)->u64 {
    x^=x>>30;x=x.wrapping_mul(0xbf58476d1ce4e5b9);
    x^=x>>27;x=x.wrapping_mul(0x94d049bb133111eb);x^(x>>31)
}
#[allow(unused_mut)]
fn fp(ast:&ExpAst,jm:&HashMap<[u8;32],u32>,cm:&HashMap<[u8;32],u32>)->u64 {match ast {
/* FINGERPRINT_ARMS */
}}
#[allow(unused_variables)]
fn contains_ind_w(ast:&ExpAst)->bool {match ast {
/* CONTAINS_W_ARMS */
}}
fn main(){
    let file=std::env::args().nth(1).expect("trace path");
    // Backported Rust kernels can check the computation steps that the original
    // 2025 source could not. Default mode retains historical compatibility.
    let corrected=std::env::args().any(|arg|arg=="--corrected-kernel");
    let lines=BufReader::new(std::fs::File::open(file).unwrap()).lines();
    let mut store=SimpleGraphStore::new();
    let mut js:HashMap<u32,JudgementHash>=HashMap::new();
    let mut cs:HashMap<u32,ContextFragmentHash>=HashMap::new();
    let mut jm=HashMap::new();let mut cm=HashMap::new();
    let mut skipped_ids=HashSet::new();let mut matched=0;let mut skipped=0;
    for (index,line) in lines.enumerate(){
        let line=line.unwrap();let mut it=line.split_whitespace().map(|x|x.parse::<u64>().unwrap());
        let op=it.next().unwrap() as u32;let nj=it.next().unwrap() as usize;
        let ji:Vec<u32>=it.by_ref().take(nj).map(|x|x as u32).collect();
        let ctx=it.next().unwrap() as u32;let nf=it.next().unwrap() as usize;
        let fi:Vec<u32>=it.by_ref().take(nf).map(|x|x as u32).collect();
        let status=it.next().unwrap();let result=it.next().unwrap() as u32;
        let expected=(it.next().unwrap(),it.next().unwrap(),it.next().unwrap());
        // Upstream WComp checks four premises but its apply_impl treats the
        // third (label) as WSup and panics. C fixes that construction defect.
        // EqComp substitutes in the motive's universe rather than the motive,
        // assigning the equality the wrong type. Its corrected C result and
        // descendants are tested directly instead of copied from this oracle.
        let corrected_w_beta = matches!(op,200|201|203) && ji.iter().any(|id| {
            js.get(id).and_then(|hash|store.lookup_judgement(hash))
                .map(|j|contains_ind_w(&j.expression)||contains_ind_w(&j._type)).unwrap_or(false)
        });
        if (!corrected&&(op==133||op==113||corrected_w_beta))||ji.iter().any(|x|skipped_ids.contains(x)){
            if result!=0&&!js.contains_key(&result){skipped_ids.insert(result);}skipped+=1;continue;
        }
        if status==2{skipped+=1;continue;}
        let deps:Vec<_>=ji.iter().map(|x|*js.get(x).unwrap()).collect();
        let frees:Vec<_>=fi.iter().map(|x|if *x==0{None}else{Some(*cs.get(x).unwrap())}).collect();
        let context=if ctx==0{None}else{Some(*cs.get(&ctx).unwrap())};
        let operation=opcode(op);
        let legal=operation.is_legal(&store,&deps,context,&frees);
        assert_eq!(legal,status==0,"legality mismatch at line {} opcode {op}",index+1);
        if !legal{matched+=1;continue;}
        let output=operation.apply(&mut store,&deps,context,&frees);
        let (ef,tf,contexts)=match output{
            Either::Left(j)=>{
                let ef=fp(&j.expression,&jm,&cm);let tf=fp(&j._type,&jm,&cm);
                jm.insert(j.hash.hash,result);js.entry(result).or_insert(j.hash);
                (ef,tf,j.context_dependencies)
            }
            Either::Right(c)=>{
                let tf=fp(&c._type,&jm,&cm);cm.insert(c.hash.hash,result);cs.entry(result).or_insert(c.hash);
                (0,tf,c.context_dependencies)
            }
        };
        let mut ids:Vec<_>=contexts.iter().map(|c|*cm.get(&c.hash).unwrap()).collect();ids.sort_unstable();ids.dedup();
        let cf=ids.iter().fold(0,|h,c|mix(h^(*c as u64)));
        assert_eq!((ef,tf,cf),expected,"output mismatch at line {} opcode {op}",index+1);
        matched+=1;
    }
    println!("{{\"matched_steps\":{matched},\"skipped_known_EqComp_WComp_W_beta_or_limits\":{skipped}}}");
}
