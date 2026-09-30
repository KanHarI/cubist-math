/* Source-shaped Nat and W use only the generic signature instructions.
 * The pre-migration primitive instruction fixture remains pinned in the
 * historical differential oracle (tools/legacy-kernel.mjs). */
#include "cubical_kernel.h"
#include "declared_nat_fixture.h"
#include <assert.h>
#include <stdio.h>

static cc_kernel *k;
static uint32_t ok(uint32_t id, const char *what, int line) {
    if (!id) { fprintf(stderr, "line %d: %s: %s\n", line, what, cc_kernel_error(k)); assert(0); }
    return id;
}
#define OK(x) ok((x), #x, __LINE__)
static cc_judgement_info info(cc_judgement_id j) { cc_judgement_info r; assert(cc_kernel_judgement(k,j,&r)); return r; }
static cc_term term(cc_judgement_id j) { return info(j).term; }
static cc_term child(cc_term t, unsigned i) { cc_term c[4]; assert(cc_kernel_node(k,t,NULL,NULL,c)); return c[i]; }
static cc_term_kind kind(cc_term t) { cc_term_kind r; assert(cc_kernel_node(k,t,&r,NULL,NULL)); return r; }
static cc_judgement_id var(cc_entry_id e) { return OK(cc_instr_variable(k,e)); }
static cc_judgement_id apply(cc_judgement_id f, cc_judgement_id x) { return OK(cc_instr_apply(k,f,x)); }
static cc_judgement_id beta(cc_judgement_id j) {
    return OK(cc_instr_step(k,OK(cc_instr_refl(k,j)),1,NULL,0,CC_STEP_BETA));
}
static cc_judgement_id at_motive(cc_judgement_id value, cc_judgement_id motive, cc_judgement_id argument) {
    return OK(cc_instr_convert(k,value,OK(cc_instr_symmetry(k,beta(apply(motive,argument))))));
}
static cc_judgement_id numeral(unsigned n) {
    cc_judgement_id result = OK(fixture_zero(k));
    while (n--) result = OK(fixture_succ(k,result));
    return result;
}
static unsigned value(cc_term n) {
    unsigned result=0;
    while (kind(n)==CC_APP) { assert(kind(child(n,0))==CC_CON); n=child(n,1); ++result; }
    uint32_t index; assert(cc_kernel_node(k,n,NULL,&index,NULL));
    assert(kind(n)==CC_CON && index==0); return result;
}
static void addition(void) {
    cc_judgement_id nat=OK(fixture_nat(k));
    cc_entry_id a=OK(cc_instr_extend(k,nat,100)), b=OK(cc_instr_extend(k,nat,101));
    cc_entry_id x=OK(cc_instr_extend(k,nat,102)), n=OK(cc_instr_extend(k,nat,103));
    cc_judgement_id motive=OK(cc_instr_lambda(k,x,nat)), at_n=apply(motive,var(n));
    cc_entry_id h=OK(cc_instr_extend(k,at_n,104));
    cc_judgement_id ih=OK(cc_instr_convert(k,var(h),beta(at_n)));
    cc_judgement_id next=at_motive(OK(fixture_succ(k,ih)),motive,OK(fixture_succ(k,var(n))));
    cc_judgement_id step=OK(cc_instr_lambda(k,n,OK(cc_instr_lambda(k,h,next))));
    cc_judgement_id elim=OK(cc_instr_eliminator(k,motive));
    elim=OK(cc_instr_eliminator_clause(k,elim,at_motive(var(a),motive,numeral(0))));
    elim=OK(cc_instr_eliminator_clause(k,elim,step));
    elim=OK(cc_instr_eliminator_close(k,elim));
    cc_judgement_id sum=OK(cc_instr_convert(k,apply(elim,var(b)),beta(apply(motive,var(b)))));
    cc_judgement_id add=OK(cc_instr_define(k,105,OK(cc_instr_lambda(k,a,OK(cc_instr_lambda(k,b,sum))))));
    cc_judgement_id five=apply(apply(add,numeral(2)),numeral(3));
    assert(info(five).type==term(nat));
    assert(value(cc_kernel_normalize(k,term(five)))==5);
    cc_judgement_id computed=OK(cc_instr_step(k,OK(cc_instr_refl(k,five)),1,NULL,0,CC_STEP_NORMALIZE));
    assert(value(info(computed).other)==5);
    /* A constructor of Unit is never silently accepted as Nat. */
    assert(!cc_instr_apply(k,OK(cc_instr_construct(k,nat,1)),OK(cc_instr_point(k))));
    cc_kernel_clear_error(k);
}
static void trees(void) {
    cc_term l0=cc_kernel_term(k,CC_LCONST,0,0,0,0,0);
    cc_judgement_id u0=OK(cc_instr_universe(k,l0)), unit=OK(cc_instr_unit(k)), empty=OK(cc_instr_void(k));
    cc_judgement_id sig=OK(cc_instr_signature_begin(k,u0,CC_UNTRUNCATED,200,0));
    cc_entry_id s=OK(cc_instr_extend(k,u0,200)), label=OK(cc_instr_extend(k,unit,201));
    cc_entry_id index=OK(cc_instr_extend(k,empty,202));
    cc_judgement_id children_type=OK(cc_instr_pi(k,index,var(s)));
    cc_entry_id children=OK(cc_instr_extend(k,children_type,203));
    sig=OK(cc_instr_signature_constructor(k,sig,OK(cc_instr_pi(k,label,OK(cc_instr_pi(k,children,var(s))))),204));
    uint32_t signature=OK(cc_instr_signature_close(k,sig));
    cc_constructor_info constructor; assert(cc_kernel_signature_constructor(k,signature,0,&constructor));
    assert(constructor.data==1 && constructor.positions==1);
    cc_judgement_id tree=OK(cc_instr_sort_begin(k,signature)), sup=OK(cc_instr_construct(k,tree,0));
    cc_entry_id v=OK(cc_instr_extend(k,empty,205));
    cc_judgement_id impossible=OK(cc_instr_abort(k,tree,var(v)));
    cc_judgement_id leaf=apply(apply(sup,OK(cc_instr_point(k))),OK(cc_instr_lambda(k,v,impossible)));
    cc_judgement_id nat=OK(fixture_nat(k));
    cc_entry_id t=OK(cc_instr_extend(k,tree,206));
    cc_judgement_id motive=OK(cc_instr_lambda(k,t,nat));
    cc_entry_id a=OK(cc_instr_extend(k,unit,207));
    cc_entry_id f=OK(cc_instr_extend(k,OK(cc_instr_pi(k,index,tree)),208));
    cc_judgement_id ih_type=OK(cc_instr_pi(k,index,apply(motive,apply(var(f),var(index)))));
    cc_entry_id ih=OK(cc_instr_extend(k,ih_type,209));
    cc_judgement_id node=apply(apply(sup,var(a)),var(f));
    cc_judgement_id result=at_motive(numeral(2),motive,node);
    cc_judgement_id clause=OK(cc_instr_lambda(k,a,OK(cc_instr_lambda(k,f,OK(cc_instr_lambda(k,ih,result))))));
    cc_judgement_id elim=OK(cc_instr_eliminator_close(k,OK(cc_instr_eliminator_clause(k,OK(cc_instr_eliminator(k,motive)),clause))));
    cc_judgement_id counted=apply(elim,leaf);
    assert(value(cc_kernel_normalize(k,term(counted)))==2);
}
static void retired_syntax(void) {
    const cc_term_kind retired[]={CC_NAT,CC_ZERO,CC_SUCC,CC_NATREC,CC_W,CC_SUP,CC_WREC};
    for (unsigned i=0;i<sizeof retired/sizeof *retired;++i) {
        assert(!cc_kernel_term(k,retired[i],0,0,0,0,0));
        assert(cc_kernel_error(k)[0]); cc_kernel_clear_error(k);
    }
}
int main(void) {
    k=cc_kernel_new(); assert(k); cc_kernel_set_extensions(k,CC_EXTENSION_H1);
    addition(); trees(); retired_syntax(); cc_kernel_free(k);
    puts("Declared Nat and W instructions compute; retired syntax is refused.");
    return 0;
}
