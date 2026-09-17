/* Generated from THTH proof construction programs. Do not edit. */
tt_id p_define_aoc(tt_engine *e);
tt_id p_define_based_path_induction(tt_engine *e);
proof_tuple p_define_eq_ops(tt_engine *e);
proof_tuple p_define_homotopy(tt_engine *e);
tt_id p_define_is_decidable(tt_engine *e);
tt_id p_define_is_set(tt_engine *e);
tt_id p_define_is_trunc(tt_engine *e);
tt_id p_define_lem(tt_engine *e);
proof_tuple p_define_nat(tt_engine *e);
tt_id p_define_not(tt_engine *e);
tt_id p_define_pi_void_unique(tt_engine *e);
proof_tuple p_define_pr(tt_engine *e);
proof_tuple p_define_propositional_truncation(tt_engine *e);
tt_id p_define_singleton(tt_engine *e);
proof_tuple p_define_two(tt_engine *e);
tt_id p_define_u0(tt_engine *e);
tt_id p_define_unit(tt_engine *e);
tt_id p_define_unit_prop_unique(tt_engine *e);
tt_id p_define_uuomega(tt_engine *e);
tt_id p_define_void(tt_engine *e);
proof_tuple p_define_wnat(tt_engine *e);
proof_tuple p_create_pr1_pr2(tt_engine *e, tt_id U0_judgement);
proof_tuple p_test_comp(tt_engine *e);
proof_tuple p_test_product_commutes(tt_engine *e);

tt_id p_define_aoc(tt_engine *e) {
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id is_set = p_define_is_set(e);
    tt_id is_set_Ux__pi_Ux_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){is_set, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id is_set_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){is_set_Ux__pi_Ux_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id x_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id x_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, x_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_A_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id B_pi_A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_A_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id B_pi_A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, B_pi_A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id B_x_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){B_pi_A_Ux_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id is_set_B_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){is_set_Ux__pi_Ux_Ux_judgement, B_x_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_xA_is_set_B_x__pi_A_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, is_set_B_x_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    proof_tuple tuple_1 = p_define_propositional_truncation(e);
    tt_id trunc_form_axiom = tuple_1.v[0];
    tt_id trunc_Ux__pi_Ux_U0_judgement = proof_step(e, TT_PiElim, (tt_id[]){trunc_form_axiom, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id trunc_B_x_U0_judgement = proof_step(e, TT_PiElim, (tt_id[]){trunc_Ux__pi_Ux_U0_judgement, B_x_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_xA_trunc_B_x__pi_A_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, trunc_B_x_U0_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id pi_xA_B_x__pi_A_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, B_x_Ux_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id reduced_trunc_Ux__pi_Ux_U0_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){trunc_Ux__pi_Ux_U0_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id trunc_pi_xA_B_x_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            reduced_trunc_Ux__pi_Ux_U0_judgement,
            pi_xA_B_x__pi_A_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id result_aoc = proof_step(e, TT_PiForm, (tt_id[]){
            pi_xA_trunc_B_x__pi_A_Ux_judgement,
            trunc_pi_xA_B_x_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id aoc_conditions = proof_step(e, TT_SigmaForm, (tt_id[]){
            is_set_A_judgement,
            pi_xA_is_set_B_x__pi_A_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id aoc_conditions_leads_to_result = proof_step(e, TT_PiForm, (tt_id[]){aoc_conditions, result_aoc}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id trunc_pi_xA_B_x_Ux__trunc_pi_xA_trunc_B_x_U0_judgement = proof_step(e, TT_PiForm, (tt_id[]){pi_A_Ux_judgement, aoc_conditions_leads_to_result}, 2, 0, (tt_id[]){B_pi_A_Ux_context}, 1, __FILE__, __LINE__);
    trunc_pi_xA_B_x_Ux__trunc_pi_xA_trunc_B_x_U0_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                Ux_UUOmega_judgement,
                trunc_pi_xA_B_x_Ux__trunc_pi_xA_trunc_B_x_U0_judgement,
            }, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    trunc_pi_xA_B_x_Ux__trunc_pi_xA_trunc_B_x_U0_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                UUOmega_UUKappa_judgement,
                trunc_pi_xA_B_x_Ux__trunc_pi_xA_trunc_B_x_U0_judgement,
            }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    return proof_step(e, TT_Axiom, (tt_id[]){trunc_pi_xA_B_x_Ux__trunc_pi_xA_trunc_B_x_U0_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

tt_id p_define_based_path_induction(tt_engine *e) {
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id x_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id x_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, x_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id z_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id z_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, z_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_A_x_z_Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){A_Ux_judgement, x_A_judgement, z_A_judgement}, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi__eq_A_x_z__Ux__UUOmega = proof_step(e, TT_PiForm, (tt_id[]){eq_A_x_z_Ux_judgement, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id pi_zA__pi__eq_A_x_z__Ux__UUOmega = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, pi__eq_A_x_z__Ux__UUOmega}, 2, 0, (tt_id[]){z_A_context}, 1, __FILE__, __LINE__);
    tt_id C_pi_zA__pi__eq_A_x_z__Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_zA__pi__eq_A_x_z__Ux__UUOmega}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id C_pi_zA__pi__eq_A_x_z__Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, C_pi_zA__pi__eq_A_x_z__Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Refl_x__eq_A_x_x_judgement = proof_step(e, TT_EqIntro, (tt_id[]){x_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id C_x__pi__eq_A_x_x__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){C_pi_zA__pi__eq_A_x_z__Ux_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id C_x_Refl_x__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            C_x__pi__eq_A_x_x__Ux_judgement,
            Refl_x__eq_A_x_x_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id y_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){z_A_context}, 1, __FILE__, __LINE__);
    tt_id y_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, y_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id C_y__pi__eq_A_x_y__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){C_pi_zA__pi__eq_A_x_z__Ux_judgement, y_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_A_x_y_Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){A_Ux_judgement, x_A_judgement, y_A_judgement}, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id p_eq_A_x_y_context = proof_step(e, TT_CtxExt, (tt_id[]){eq_A_x_y_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id p_eq_A_x_y_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, p_eq_A_x_y_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id C_y_p__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            C_y__pi__eq_A_x_y__Ux_judgement,
            p_eq_A_x_y_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_C_x_Refl_x__C_y_p__Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){C_x_Refl_x__Ux_judgement, C_y_p__Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id x_y_p_D_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            pi_zA__pi__eq_A_x_z__Ux__UUOmega,
            pi_C_x_Refl_x__C_y_p__Ux_judgement,
        }, 2, 0, (tt_id[]){C_pi_zA__pi__eq_A_x_z__Ux_context}, 1, __FILE__, __LINE__);
    tt_id _x_y_D__pi_eq_A_x_y_Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){eq_A_x_y_Ux_judgement, x_y_p_D_Ux_judgement}, 2, 0, (tt_id[]){p_eq_A_x_y_context}, 1, __FILE__, __LINE__);
    tt_id q__C_x_Refl_x_context = proof_step(e, TT_CtxExt, (tt_id[]){C_x_Refl_x__Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id q__C_x_Refl_x_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, q__C_x_Refl_x_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_q_q__pi_C_x_Refl_x__C_x_Refl_x_judgement = proof_step(e, TT_PiIntro, (tt_id[]){C_x_Refl_x__Ux_judgement, q__C_x_Refl_x_judgement}, 2, 0, (tt_id[]){q__C_x_Refl_x_context}, 1, __FILE__, __LINE__);
    tt_id d_D_x_x_Refl_x_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_zA__pi__eq_A_x_z__Ux__UUOmega,
            lam_q_q__pi_C_x_Refl_x__C_x_Refl_x_judgement,
        }, 2, 0, (tt_id[]){C_pi_zA__pi__eq_A_x_z__Ux_context}, 1, __FILE__, __LINE__);
    tt_id eq_induction_path_induction = proof_step(e, TT_EqElim, (tt_id[]){
            x_y_p_D_Ux_judgement,
            d_D_x_x_Refl_x_judgement,
            x_A_judgement,
            y_A_judgement,
            p_eq_A_x_y_judgement,
        }, 5, 0, (tt_id[]){
            x_A_context,
            y_A_context,
            p_eq_A_x_y_context,
            x_A_context,
        }, 4, __FILE__, __LINE__);
    tt_id Ux_A_x_C_y_p_eq_induction_path_C = proof_step(e, TT_PiElim, (tt_id[]){
            eq_induction_path_induction,
            C_pi_zA__pi__eq_A_x_z__Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_x_C_y_eq_induction_path_C = proof_step(e, TT_PiIntro, (tt_id[]){
            eq_A_x_y_Ux_judgement,
            Ux_A_x_C_y_p_eq_induction_path_C,
        }, 2, 0, (tt_id[]){p_eq_A_x_y_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_x_C_eq_induction_path_C = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_x_C_y_eq_induction_path_C}, 2, 0, (tt_id[]){y_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_x_eq_induction_path_C = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_zA__pi__eq_A_x_z__Ux__UUOmega,
            Ux_A_x_C_eq_induction_path_C,
        }, 2, 0, (tt_id[]){C_pi_zA__pi__eq_A_x_z__Ux_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_eq_induction_path_C = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_x_eq_induction_path_C}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_eq_induction_path_C = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_eq_induction_path_C}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id eq_induction_path_C = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_eq_induction_path_C}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id defeq_path_induction_judgement = proof_step(e, TT_Def, (tt_id[]){eq_induction_path_C}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_path_induction_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

proof_tuple p_define_eq_ops(tt_engine *e) {
    tt_id _U0_U1_judgement = p_define_u0(e);
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id based_path_induction_judgement = p_define_based_path_induction(e);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id x_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id x_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, x_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id y_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id y_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, y_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id z_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){y_A_context}, 1, __FILE__, __LINE__);
    tt_id z_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, z_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_A_x_y_Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){A_Ux_judgement, x_A_judgement, y_A_judgement}, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_A_y_x_Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){A_Ux_judgement, y_A_judgement, x_A_judgement}, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id p_eq_A_x_y_context = proof_step(e, TT_CtxExt, (tt_id[]){eq_A_x_y_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id p_eq_A_x_y_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, p_eq_A_x_y_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id refl_x_eq_A_x_x_judgement = proof_step(e, TT_EqIntro, (tt_id[]){x_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id IndEq_z_Refl_z_x_y_p_eq_A_y_x_judgement = proof_step(e, TT_EqElim, (tt_id[]){
            eq_A_y_x_Ux_judgement,
            refl_x_eq_A_x_x_judgement,
            x_A_judgement,
            y_A_judgement,
            p_eq_A_x_y_judgement,
        }, 5, 0, (tt_id[]){
            x_A_context,
            y_A_context,
            0,
            x_A_context,
        }, 4, __FILE__, __LINE__);
    tt_id Ux_A_x_y_eq_inverse_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            eq_A_x_y_Ux_judgement,
            IndEq_z_Refl_z_x_y_p_eq_A_y_x_judgement,
        }, 2, 0, (tt_id[]){p_eq_A_x_y_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_x_eq_inverse_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_x_y_eq_inverse_judgement}, 2, 0, (tt_id[]){y_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_eq_inverse_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_x_eq_inverse_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_eq_inverse_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_eq_inverse_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id eq_inverse_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_eq_inverse_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id eq_inv_defeq_judgement = proof_step(e, TT_Def, (tt_id[]){eq_inverse_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id inv_eq_def = proof_step(e, TT_DefEqExtL, (tt_id[]){eq_inv_defeq_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_A_y_z_Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){A_Ux_judgement, y_A_judgement, z_A_judgement}, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id q_eq_A_y_z_context = proof_step(e, TT_CtxExt, (tt_id[]){eq_A_y_z_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id q_eq_A_y_z_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, q_eq_A_y_z_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id basedPathInduction_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            based_path_induction_judgement,
            Ux_UUOmega_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id basedPathInduction_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){basedPathInduction_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id basedPathInduction_Ux_A_y_judgement = proof_step(e, TT_PiElim, (tt_id[]){basedPathInduction_Ux_A_judgement, y_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_A_x_z_Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){A_Ux_judgement, x_A_judgement, z_A_judgement}, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_p_eq_A_x_z__pi_eq_A_y_x__Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){eq_A_y_x_Ux_judgement, eq_A_x_z_Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id lam_x_p_eq_A_x_z__pi_eq_A_y_x__Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            A_Ux_judgement,
            lam_p_eq_A_x_z__pi_eq_A_y_x__Ux_judgement,
        }, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id basedPathInduction_Ux_A_y_lam_x_p_eq_A_x_z__pi_eq_A_y_x__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
                basedPathInduction_Ux_A_y_judgement,
                lam_x_p_eq_A_x_z__pi_eq_A_y_x__Ux_judgement,
            }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    basedPathInduction_Ux_A_y_lam_x_p_eq_A_x_z__pi_eq_A_y_x__Ux_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){basedPathInduction_Ux_A_y_lam_x_p_eq_A_x_z__pi_eq_A_y_x__Ux_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id basedPathInd_eq_eq_r_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            basedPathInduction_Ux_A_y_lam_x_p_eq_A_x_z__pi_eq_A_y_x__Ux_judgement,
            x_A_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_inv_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){inv_eq_def, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_inv_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){eq_inv_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_inv_Ux_A_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){eq_inv_Ux_A_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_inv_Ux_A_x_y_judgement = proof_step(e, TT_PiElim, (tt_id[]){eq_inv_Ux_A_x_judgement, y_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_inv_Ux_A_x_y_p_judgement = proof_step(e, TT_PiElim, (tt_id[]){eq_inv_Ux_A_x_y_judgement, p_eq_A_x_y_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id basedPathInd_eq_eq_r_eq_inv_Ux_A_x_y_p_judgement = proof_step(e, TT_PiElim, (tt_id[]){
                basedPathInd_eq_eq_r_judgement,
                eq_inv_Ux_A_x_y_p_judgement,
            }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id basedPathInd_eq_eq_r_eq_inv_Ux_A_x_y_p_q_judgement = proof_step(e, TT_PiElim, (tt_id[]){
                basedPathInd_eq_eq_r_eq_inv_Ux_A_x_y_p_judgement,
                q_eq_A_y_z_judgement,
            }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_x_y_z_p_cat_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            eq_A_y_z_Ux_judgement,
            basedPathInd_eq_eq_r_eq_inv_Ux_A_x_y_p_q_judgement,
        }, 2, 0, (tt_id[]){q_eq_A_y_z_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_x_y_z_cat_judgement = proof_step(e, TT_PiIntro, (tt_id[]){eq_A_x_y_Ux_judgement, Ux_A_x_y_z_p_cat_judgement}, 2, 0, (tt_id[]){p_eq_A_x_y_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_x_y_cat_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_x_y_z_cat_judgement}, 2, 0, (tt_id[]){z_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_x_cat_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_x_y_cat_judgement}, 2, 0, (tt_id[]){y_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_cat_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_x_cat_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_cat_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_cat_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id cat_eq_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_cat_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id cat_eq_defeq_judgement = proof_step(e, TT_Def, (tt_id[]){cat_eq_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id cat_eq_def = proof_step(e, TT_DefEqExtL, (tt_id[]){cat_eq_defeq_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id cateq_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){cat_eq_def, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id cateq_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){cateq_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id cateq_Ux_A_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){cateq_Ux_A_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id cateq_Ux_A_x_y_judgement = proof_step(e, TT_PiElim, (tt_id[]){cateq_Ux_A_x_judgement, y_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id cateq_Ux_A_x_y_z_judgement = proof_step(e, TT_PiElim, (tt_id[]){cateq_Ux_A_x_y_judgement, z_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id cateq_Ux_A_x_y_z_p_judgement = proof_step(e, TT_PiElim, (tt_id[]){cateq_Ux_A_x_y_z_judgement, p_eq_A_x_y_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id _cateq_Ux_A_x_y_z_p_q_judgement = proof_step(e, TT_PiElim, (tt_id[]){cateq_Ux_A_x_y_z_p_judgement, q_eq_A_y_z_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eqinv_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){inv_eq_def, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eqinv_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){eqinv_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eqinv_Ux_A_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){eqinv_Ux_A_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id _eqinv_Ux_A_x_z_judgement = proof_step(e, TT_PiElim, (tt_id[]){eqinv_Ux_A_x_judgement, z_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id cateq_Ux_A_x_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){cateq_Ux_A_x_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id cateq_Ux_A_x_x_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){cateq_Ux_A_x_x_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id cateq_Ux_A_x_x_x_refl_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            cateq_Ux_A_x_x_x_judgement,
            refl_x_eq_A_x_x_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id cateq_Ux_A_x_x_x_refl_refl_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            cateq_Ux_A_x_x_x_refl_judgement,
            refl_x_eq_A_x_x_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id defeq_refl_cateq_refl_refl_judgement = proof_step(e, TT_DefEqRefl, (tt_id[]){cateq_Ux_A_x_x_x_refl_refl_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    defeq_refl_cateq_refl_refl_judgement = proof_step(e, TT_HighExp, (tt_id[]){defeq_refl_cateq_refl_refl_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    defeq_refl_cateq_refl_refl_judgement = proof_step(e, TT_High1, (tt_id[]){defeq_refl_cateq_refl_refl_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_1=0; loop_1<4; ++loop_1) {
    defeq_refl_cateq_refl_refl_judgement = proof_step(e, TT_DefBetaReduceGrossKnuth, (tt_id[]){defeq_refl_cateq_refl_refl_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id lam_x_cat_refl_refl_is_refl = proof_step(e, TT_PiIntro, (tt_id[]){
            A_Ux_judgement,
            defeq_refl_cateq_refl_refl_judgement,
        }, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id lam_A_lam_x_cat_refl_refl_is_refl = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, lam_x_cat_refl_refl_is_refl}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id cat_refl_refl_is_refl = proof_step(e, TT_PiIntro, (tt_id[]){
            UUOmega_UUKappa_judgement,
            lam_A_lam_x_cat_refl_refl_is_refl,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id eqinv_Ux_A_x_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){eqinv_Ux_A_x_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eqinv_Ux_A_x_x_refl_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            eqinv_Ux_A_x_x_judgement,
            refl_x_eq_A_x_x_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id defeq_inv_refl_judgement = proof_step(e, TT_DefEqRefl, (tt_id[]){eqinv_Ux_A_x_x_refl_x_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    defeq_inv_refl_judgement = proof_step(e, TT_HighExp, (tt_id[]){defeq_inv_refl_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    defeq_inv_refl_judgement = proof_step(e, TT_High1, (tt_id[]){defeq_inv_refl_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_2=0; loop_2<2; ++loop_2) {
    defeq_inv_refl_judgement = proof_step(e, TT_DefBetaReduceGrossKnuth, (tt_id[]){defeq_inv_refl_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id Ux_A_defeq_inv_refl_refl_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, defeq_inv_refl_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_defeq_inv_refl_refl_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            Ux_UUOmega_judgement,
            Ux_A_defeq_inv_refl_refl_judgement,
        }, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id defeq_inv_refl_refl_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            UUOmega_UUKappa_judgement,
            Ux_defeq_inv_refl_refl_judgement,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id eqinv_Ux_A_x_y_judgement = proof_step(e, TT_PiElim, (tt_id[]){eqinv_Ux_A_x_judgement, y_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eqinv_Ux_A_x_y_p_judgement = proof_step(e, TT_PiElim, (tt_id[]){eqinv_Ux_A_x_y_judgement, p_eq_A_x_y_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eqinv_Ux_A_y_judgement = proof_step(e, TT_PiElim, (tt_id[]){eqinv_Ux_A_judgement, y_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eqinv_Ux_A_y_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){eqinv_Ux_A_y_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eqinv_Ux_A_y_x_eqinv_Ux_A_x_y_p_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            eqinv_Ux_A_y_x_judgement,
            eqinv_Ux_A_x_y_p_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_eq_A_x_y__inv_inv_p__p___Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){
            eq_A_x_y_Ux_judgement,
            eqinv_Ux_A_y_x_eqinv_Ux_A_x_y_p_judgement,
            p_eq_A_x_y_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id refl_refl_x_judgement = proof_step(e, TT_EqIntro, (tt_id[]){refl_x_eq_A_x_x_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id defeq_refl_inv_refl_judgement = proof_step(e, TT_DefEqSwp, (tt_id[]){defeq_inv_refl_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id refl_refl_for_inv_inv_id_judgement = proof_step(e, TT_HighType, (tt_id[]){refl_refl_x_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_refl_for_inv_inv_id_judgement = proof_step(e, TT_High1, (tt_id[]){refl_refl_for_inv_inv_id_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_refl_for_inv_inv_id_judgement = proof_step(e, TT_HighSubs, (tt_id[]){
            refl_refl_for_inv_inv_id_judgement,
            defeq_refl_inv_refl_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_refl_for_inv_inv_id_judgement = proof_step(e, TT_HighSubs, (tt_id[]){
            refl_refl_for_inv_inv_id_judgement,
            defeq_refl_inv_refl_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_x_y_p_inv_inv_is_id_judgement = proof_step(e, TT_EqElim, (tt_id[]){
            eq_eq_A_x_y__inv_inv_p__p___Ux_judgement,
            refl_refl_for_inv_inv_id_judgement,
            x_A_judgement,
            y_A_judgement,
            p_eq_A_x_y_judgement,
        }, 5, 0, (tt_id[]){
            x_A_context,
            y_A_context,
            p_eq_A_x_y_context,
            x_A_context,
        }, 4, __FILE__, __LINE__);
    tt_id Ux_A_x_y_inv_inv_is_id_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            eq_A_x_y_Ux_judgement,
            Ux_A_x_y_p_inv_inv_is_id_judgement,
        }, 2, 0, (tt_id[]){p_eq_A_x_y_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_x_inv_inv_is_id_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_x_y_inv_inv_is_id_judgement}, 2, 0, (tt_id[]){y_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_inv_inv_is_id_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_x_inv_inv_is_id_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_inv_inv_is_id_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_inv_inv_is_id_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id inv_inv_is_id_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            UUOmega_UUKappa_judgement,
            Ux_inv_inv_is_id_judgement,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id defeq_inv_inv_is_id = proof_step(e, TT_Def, (tt_id[]){inv_inv_is_id_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_inv_inv_is_id = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_inv_inv_is_id}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return (proof_tuple){{inv_eq_def, defeq_inv_refl_refl_judgement, def_inv_inv_is_id, cat_eq_def, cat_refl_refl_is_refl}};
}

proof_tuple p_define_homotopy(tt_engine *e) {
    proof_tuple tuple_1 = p_define_pr(e);
    tt_id def_pr1 = tuple_1.v[0];
    tt_id _def_pr2 = tuple_1.v[1];
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_A_Ux__UUOmega_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id B__pi_A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_A_Ux__UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id B__pi_A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, B__pi_A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id x_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id x_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, x_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id B_x__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){B__pi_A_Ux_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_x_A_B_x__Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, B_x__Ux_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id f__pi_x_A_B_x_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_x_A_B_x__Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id f__pi_x_A_B_x_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, f__pi_x_A_B_x_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id g__pi_x_A_B_x_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_x_A_B_x__Ux_judgement}, 1, 0, (tt_id[]){f__pi_x_A_B_x_context}, 1, __FILE__, __LINE__);
    tt_id g__pi_x_A_B_x_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, g__pi_x_A_B_x_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_x__B_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){f__pi_x_A_B_x_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id g_x__B_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){g__pi_x_A_B_x_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_B_x_f_x_g_x__Ux = proof_step(e, TT_EqForm, (tt_id[]){
            B_x__Ux_judgement,
            f_x__B_x_judgement,
            g_x__B_x_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_x_A_eq_B_x_f_x_g_x__Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, eq_B_x_f_x_g_x__Ux}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id lam_g__pi_x_A_eq_B_x_f_x_g_x__Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_x_A_B_x__Ux_judgement,
            pi_x_A_eq_B_x_f_x_g_x__Ux_judgement,
        }, 2, 0, (tt_id[]){g__pi_x_A_B_x_context}, 1, __FILE__, __LINE__);
    tt_id lam_f__lam_g__pi_x_A_eq_B_x_f_x_g_x__Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
                pi_x_A_B_x__Ux_judgement,
                lam_g__pi_x_A_eq_B_x_f_x_g_x__Ux_judgement,
            }, 2, 0, (tt_id[]){f__pi_x_A_B_x_context}, 1, __FILE__, __LINE__);
    tt_id lam_B__lam_f__lam_g__pi_x_A_eq_B_x_f_x_g_x__Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
                pi_A_Ux__UUOmega_judgement,
                lam_f__lam_g__pi_x_A_eq_B_x_f_x_g_x__Ux_judgement,
            }, 2, 0, (tt_id[]){B__pi_A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id Ux_homotopy_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            Ux_UUOmega_judgement,
            lam_B__lam_f__lam_g__pi_x_A_eq_B_x_f_x_g_x__Ux_judgement,
        }, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id homotopy_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_homotopy_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id defeq_homotopy = proof_step(e, TT_Def, (tt_id[]){homotopy_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_homotopy = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_homotopy}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_pi_x_A_B_x__f__g__Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){
            pi_x_A_B_x__Ux_judgement,
            f__pi_x_A_B_x_judgement,
            g__pi_x_A_B_x_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id p__eq_pi_x_A_B_x__f__g__Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){eq_pi_x_A_B_x__f__g__Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id p__eq_pi_x_A_B_x__f__g__Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, p__eq_pi_x_A_B_x__f__g__Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    f_x__B_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){f__pi_x_A_B_x_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id refl_f_x__eq_B_x__f_x__f_x__judgement = proof_step(e, TT_EqIntro, (tt_id[]){f_x__B_x_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_x_refl_f_x__pi_x_A__eq_B_x__fx__fx__judgement = proof_step(e, TT_PiIntro, (tt_id[]){
                A_Ux_judgement,
                refl_f_x__eq_B_x__f_x__f_x__judgement,
            }, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id happly_Ux_A_B_f_g_p__judgement = proof_step(e, TT_EqElim, (tt_id[]){
            pi_x_A_eq_B_x_f_x_g_x__Ux_judgement,
            lam_x_refl_f_x__pi_x_A__eq_B_x__fx__fx__judgement,
            f__pi_x_A_B_x_judgement,
            g__pi_x_A_B_x_judgement,
            p__eq_pi_x_A_B_x__f__g__Ux_judgement,
        }, 5, 0, (tt_id[]){
            f__pi_x_A_B_x_context,
            g__pi_x_A_B_x_context,
            0,
            f__pi_x_A_B_x_context,
        }, 4, __FILE__, __LINE__);
    tt_id homotopy_Ux__pi_A_Ux_pi_B_pi_A_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_homotopy, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_A__pi_B_pi_A_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            homotopy_Ux__pi_A_Ux_pi_B_pi_A_Ux_judgement,
            A_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_A_B__pi_A_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            homotopy_Ux_A__pi_B_pi_A_Ux_judgement,
            B__pi_A_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_A_B_f__pi_A_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            homotopy_Ux_A_B__pi_A_Ux_judgement,
            f__pi_x_A_B_x_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_A_B_f_g__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            homotopy_Ux_A_B_f__pi_A_Ux_judgement,
            g__pi_x_A_B_x_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_parametrized_defeq_refl_judgement = proof_step(e, TT_DefEqRefl, (tt_id[]){homotopy_Ux_A_B_f_g__Ux_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_parametrized_exp_highlight_judgement = proof_step(e, TT_HighExp, (tt_id[]){homotopy_parametrized_defeq_refl_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_parametrized_exp_highlight_rhs_judgement = proof_step(e, TT_High0, (tt_id[]){homotopy_parametrized_exp_highlight_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_A_B_f_g_eval_judgement = proof_step(e, TT_HighSubs, (tt_id[]){
            homotopy_parametrized_exp_highlight_rhs_judgement,
            defeq_homotopy,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_2=0; loop_2<5; ++loop_2) {
    homotopy_Ux_A_B_f_g_eval_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){homotopy_Ux_A_B_f_g_eval_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id happly_homotopy__judgement = proof_step(e, TT_Subs, (tt_id[]){
            happly_Ux_A_B_f_g_p__judgement,
            homotopy_Ux_A_B_f_g_eval_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id happly_Ux_A_B_f_g__judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            eq_pi_x_A_B_x__f__g__Ux_judgement,
            happly_homotopy__judgement,
        }, 2, 0, (tt_id[]){p__eq_pi_x_A_B_x__f__g__Ux_context}, 1, __FILE__, __LINE__);
    tt_id happly_Ux_A_B_f__judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_x_A_B_x__Ux_judgement,
            happly_Ux_A_B_f_g__judgement,
        }, 2, 0, (tt_id[]){g__pi_x_A_B_x_context}, 1, __FILE__, __LINE__);
    tt_id happly_Ux_A_B__judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_x_A_B_x__Ux_judgement,
            happly_Ux_A_B_f__judgement,
        }, 2, 0, (tt_id[]){f__pi_x_A_B_x_context}, 1, __FILE__, __LINE__);
    tt_id happly_Ux_A__judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_A_Ux__UUOmega_judgement,
            happly_Ux_A_B__judgement,
        }, 2, 0, (tt_id[]){B__pi_A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id happly_Ux__judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, happly_Ux_A__judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id happly__judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, happly_Ux__judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id defeq_happly = proof_step(e, TT_Def, (tt_id[]){happly__judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_happly = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_happly}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id C_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id C_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, C_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_A_C__Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, C_Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id y_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id y_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, y_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_A_x_y__Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){A_Ux_judgement, x_A_judgement, y_A_judgement}, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id p_eq_A_x_y_context = proof_step(e, TT_CtxExt, (tt_id[]){eq_A_x_y__Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id p_eq_A_x_y_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, p_eq_A_x_y_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_pi_A_C_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_A_C__Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id f_pi_A_C_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, f_pi_A_C_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_x__C_judgement = proof_step(e, TT_PiElim, (tt_id[]){f_pi_A_C_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_y__C_judgement = proof_step(e, TT_PiElim, (tt_id[]){f_pi_A_C_judgement, y_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_C_f_x_f_y__Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){
            C_Ux_judgement,
            f_x__C_judgement,
            f_y__C_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Refl_f_x__C_judgement = proof_step(e, TT_EqIntro, (tt_id[]){f_x__C_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ind_eq_C_f_x_f_y__Ux_judgement = proof_step(e, TT_EqElim, (tt_id[]){
            eq_C_f_x_f_y__Ux_judgement,
            Refl_f_x__C_judgement,
            x_A_judgement,
            y_A_judgement,
            p_eq_A_x_y_judgement,
        }, 5, 0, (tt_id[]){
            x_A_context,
            y_A_context,
            0,
            x_A_context,
        }, 4, __FILE__, __LINE__);
    tt_id Ux_A_C_f_x_y_ap_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            eq_A_x_y__Ux_judgement,
            Ind_eq_C_f_x_f_y__Ux_judgement,
        }, 2, 0, (tt_id[]){p_eq_A_x_y_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_C_f_x_ap_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_C_f_x_y_ap_judgement}, 2, 0, (tt_id[]){y_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_C_f_ap_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_C_f_x_ap_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_C_ap_judgement = proof_step(e, TT_PiIntro, (tt_id[]){pi_A_C__Ux_judgement, Ux_A_C_f_ap_judgement}, 2, 0, (tt_id[]){f_pi_A_C_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_ap_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_C_ap_judgement}, 2, 0, (tt_id[]){C_Ux_context}, 1, __FILE__, __LINE__);
    tt_id Ux_ap_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_ap_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id ap_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_ap_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id ap_defeq_judgement = proof_step(e, TT_Def, (tt_id[]){ap_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_ap = proof_step(e, TT_DefEqExtL, (tt_id[]){ap_defeq_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_id_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, x_A_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_id_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_id_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id id_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_id_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id id_defeq_judgement = proof_step(e, TT_Def, (tt_id[]){id_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_id = proof_step(e, TT_DefEqExtL, (tt_id[]){id_defeq_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_C_A__Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){C_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id g_pi_C_A_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_C_A__Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id g_pi_C_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, g_pi_C_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id c_C_context = proof_step(e, TT_CtxExt, (tt_id[]){C_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id c_C_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, c_C_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id g_c_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){g_pi_C_A_judgement, c_C_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_g_c_C_judgement = proof_step(e, TT_PiElim, (tt_id[]){f_pi_A_C_judgement, g_c_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_g__C_C_judgement = proof_step(e, TT_PiIntro, (tt_id[]){C_Ux_judgement, f_g_c_C_judgement}, 2, 0, (tt_id[]){c_C_context}, 1, __FILE__, __LINE__);
    tt_id homotopy_Ux_C_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            homotopy_Ux__pi_A_Ux_pi_B_pi_A_Ux_judgement,
            C_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_c_C__Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){C_Ux_judgement, C_Ux_judgement}, 2, 0, (tt_id[]){c_C_context}, 1, __FILE__, __LINE__);
    tt_id homotopy_Ux_C_C_judgement = proof_step(e, TT_PiElim, (tt_id[]){homotopy_Ux_C_judgement, lam_c_C__Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_C_C_reduced_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){homotopy_Ux_C_C_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_C_f_g_c_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            homotopy_Ux_C_C_reduced_judgement,
            f_g__C_C_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_id, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_Ux_C_judgement = proof_step(e, TT_PiElim, (tt_id[]){id_Ux_judgement, C_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    homotopy_Ux_C_f_g_c_judgement = proof_step(e, TT_PiElim, (tt_id[]){homotopy_Ux_C_f_g_c_judgement, id_Ux_C_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_C_f_g_c_refl_judgement = proof_step(e, TT_DefEqRefl, (tt_id[]){homotopy_Ux_C_f_g_c_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_C_f_g_c_refl_exphigh_judgement = proof_step(e, TT_HighExp, (tt_id[]){homotopy_Ux_C_f_g_c_refl_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_C_f_g_c_highright_judgement = proof_step(e, TT_High1, (tt_id[]){homotopy_Ux_C_f_g_c_refl_exphigh_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pre_homotopy_Ux_C_f_g_c_eval_judgement = proof_step(e, TT_HighSubs, (tt_id[]){
            homotopy_Ux_C_f_g_c_highright_judgement,
            defeq_homotopy,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_C_f_g_c_eval_judgement = proof_step(e, TT_HighSubs, (tt_id[]){
            pre_homotopy_Ux_C_f_g_c_eval_judgement,
            id_defeq_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned _i=0; _i<5; ++_i) {
    homotopy_Ux_C_f_g_c_eval_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){homotopy_Ux_C_f_g_c_eval_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id epsilon_homotopy_f_g_id_C_context = proof_step(e, TT_CtxExt, (tt_id[]){homotopy_Ux_C_f_g_c_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id epsilon_homotopy_f_g_id_C_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, epsilon_homotopy_f_g_id_C_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id epsilon_subs_judgement = proof_step(e, TT_Subs, (tt_id[]){
            epsilon_homotopy_f_g_id_C_judgement,
            homotopy_Ux_C_f_g_c_eval_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id epsilon_f_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){epsilon_subs_judgement, f_x__C_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            homotopy_Ux__pi_A_Ux_pi_B_pi_A_Ux_judgement,
            A_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_x_A__pi_A_Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id homotopy_Ux_A_xA_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            homotopy_Ux_A_judgement,
            lam_x_A__pi_A_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id reduced_homotopy_Ux_A_xA_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){homotopy_Ux_A_xA_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    f_x__C_judgement = proof_step(e, TT_PiElim, (tt_id[]){f_pi_A_C_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id g_f_x__A_judgement = proof_step(e, TT_PiElim, (tt_id[]){g_pi_C_A_judgement, f_x__C_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_g_f_x__A_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, g_f_x__A_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id id_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){id_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_g_f_x__judgement = proof_step(e, TT_PiElim, (tt_id[]){
            reduced_homotopy_Ux_A_xA_judgement,
            lam_g_f_x__A_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_g_f_x_id_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){homotopy_g_f_x__judgement, id_Ux_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eta_context = proof_step(e, TT_CtxExt, (tt_id[]){homotopy_g_f_x_id_A_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id eta_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, eta_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eta_judgement_sub1 = proof_step(e, TT_Subs, (tt_id[]){eta_judgement, defeq_homotopy}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eta_judgement_sub2 = proof_step(e, TT_Subs, (tt_id[]){eta_judgement_sub1, id_defeq_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_4=0; loop_4<3; ++loop_4) {
    eta_judgement_sub2 = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){eta_judgement_sub2}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id ap_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_ap, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ap_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){ap_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ap_Ux_A_C_judgement = proof_step(e, TT_PiElim, (tt_id[]){ap_Ux_A_judgement, C_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ap_Ux_A_C_f_judgement = proof_step(e, TT_PiElim, (tt_id[]){ap_Ux_A_C_judgement, f_pi_A_C_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ap_Ux_A_C_f_g_f_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){ap_Ux_A_C_f_judgement, g_f_x__A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ap_Ux_A_C_f_g_f_x_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){ap_Ux_A_C_f_g_f_x_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eta_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){eta_judgement_sub2, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ap_Ux_A_C_f_g_f_x_x_eta_judgement = proof_step(e, TT_PiElim, (tt_id[]){ap_Ux_A_C_f_g_f_x_x_judgement, eta_x_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_g_f_x_C_judgement = proof_step(e, TT_PiElim, (tt_id[]){f_pi_A_C_judgement, g_f_x__A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq__C__f_g_f_x___f_x__Ux = proof_step(e, TT_EqForm, (tt_id[]){
            C_Ux_judgement,
            f_g_f_x_C_judgement,
            f_x__C_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq__eq_C_fgfx_fx__ap_f_gfx_x_eta_x__epsilon_fx__ux = proof_step(e, TT_EqForm, (tt_id[]){
                eq__C__f_g_f_x___f_x__Ux,
                ap_Ux_A_C_f_g_f_x_x_eta_judgement,
                epsilon_f_x_judgement,
            }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_x_A_hom2_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            A_Ux_judgement,
            eq__eq_C_fgfx_fx__ap_f_gfx_x_eta_x__epsilon_fx__ux,
        }, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id sigma_epsion_hom2_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){
            homotopy_Ux_C_f_g_c_judgement,
            pi_x_A_hom2_judgement,
        }, 2, 0, (tt_id[]){epsilon_homotopy_f_g_id_C_context}, 1, __FILE__, __LINE__);
    tt_id sigma_eta_sigma_epsilon_pi_x_hom2_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){
                homotopy_g_f_x_id_A_judgement,
                sigma_epsion_hom2_judgement,
            }, 2, 0, (tt_id[]){eta_context}, 1, __FILE__, __LINE__);
    tt_id sigma_g_sigma_eta_sigma_epsilon_pi_x_hom2_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){
                pi_C_A__Ux_judgement,
                sigma_eta_sigma_epsilon_pi_x_hom2_judgement,
            }, 2, 0, (tt_id[]){g_pi_C_A_context}, 1, __FILE__, __LINE__);
    tt_id lam_f_isequiv = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_A_C__Ux_judgement,
            sigma_g_sigma_eta_sigma_epsilon_pi_x_hom2_judgement,
        }, 2, 0, (tt_id[]){f_pi_A_C_context}, 1, __FILE__, __LINE__);
    tt_id lam_C_lam_f_isequiv = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, lam_f_isequiv}, 2, 0, (tt_id[]){C_Ux_context}, 1, __FILE__, __LINE__);
    lam_C_lam_f_isequiv = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, lam_C_lam_f_isequiv}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id isequiv_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, lam_C_lam_f_isequiv}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id isequiv_defeq_judgement = proof_step(e, TT_Def, (tt_id[]){isequiv_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_isequiv = proof_step(e, TT_DefEqExtL, (tt_id[]){isequiv_defeq_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_B_f_g_funext_type = proof_step(e, TT_PiForm, (tt_id[]){
            homotopy_Ux_A_B_f_g__Ux_judgement,
            eq_pi_x_A_B_x__f__g__Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_A_B_f_funext_type = proof_step(e, TT_PiForm, (tt_id[]){pi_x_A_B_x__Ux_judgement, Ux_A_B_f_g_funext_type}, 2, 0, (tt_id[]){g__pi_x_A_B_x_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_B_funext_type = proof_step(e, TT_PiForm, (tt_id[]){pi_x_A_B_x__Ux_judgement, Ux_A_B_f_funext_type}, 2, 0, (tt_id[]){f__pi_x_A_B_x_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_funext_type = proof_step(e, TT_PiForm, (tt_id[]){pi_A_Ux__UUOmega_judgement, Ux_A_B_funext_type}, 2, 0, (tt_id[]){B__pi_A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id Ux_funext_type = proof_step(e, TT_PiForm, (tt_id[]){Ux_UUOmega_judgement, Ux_A_funext_type}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id funext_type = proof_step(e, TT_PiForm, (tt_id[]){UUOmega_UUKappa_judgement, Ux_funext_type}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id funext_axiom = proof_step(e, TT_Axiom, (tt_id[]){funext_type}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id h_homotopy_A_B_f_g_context = proof_step(e, TT_CtxExt, (tt_id[]){homotopy_Ux_A_B_f_g__Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id h_homotopy_A_B_f_g_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, h_homotopy_A_B_f_g_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){funext_axiom, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){funext_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_A_B_judgement = proof_step(e, TT_PiElim, (tt_id[]){funext_Ux_A_judgement, B__pi_A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_A_B_f_judgement = proof_step(e, TT_PiElim, (tt_id[]){funext_Ux_A_B_judgement, f__pi_x_A_B_x_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_A_B_f_g_judgement = proof_step(e, TT_PiElim, (tt_id[]){funext_Ux_A_B_f_judgement, g__pi_x_A_B_x_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_A_B_f_g_h_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            funext_Ux_A_B_f_g_judgement,
            h_homotopy_A_B_f_g_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id happly_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_happly, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id happly_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){happly_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id happly_Ux_A_B_judgement = proof_step(e, TT_PiElim, (tt_id[]){happly_Ux_A_judgement, B__pi_A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id happly_Ux_A_B_f_judgement = proof_step(e, TT_PiElim, (tt_id[]){happly_Ux_A_B_judgement, f__pi_x_A_B_x_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id happly_Ux_A_B_f_g_judgement = proof_step(e, TT_PiElim, (tt_id[]){happly_Ux_A_B_f_judgement, g__pi_x_A_B_x_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id happly_Ux_A_B_f_g_funext_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            happly_Ux_A_B_f_g_judgement,
            funext_Ux_A_B_f_g_h_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    happly_Ux_A_B_f_g_funext_judgement = proof_step(e, TT_Subs, (tt_id[]){happly_Ux_A_B_f_g_funext_judgement, defeq_homotopy}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    happly_Ux_A_B_f_g_funext_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){happly_Ux_A_B_f_g_funext_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id happly_Ux_A_B_f_g_funext_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){happly_Ux_A_B_f_g_funext_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id h_reduced_judgement = proof_step(e, TT_Subs, (tt_id[]){h_homotopy_A_B_f_g_judgement, defeq_homotopy}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    h_reduced_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){h_reduced_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id h_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){h_reduced_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_B_x__f_x__g_x_judgement = proof_step(e, TT_EqForm, (tt_id[]){
            B_x__Ux_judgement,
            f_x__B_x_judgement,
            g_x__B_x_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_B_f_g_h_x_happly_funext_h_x_judgement = proof_step(e, TT_EqForm, (tt_id[]){
            eq_B_x__f_x__g_x_judgement,
            happly_Ux_A_B_f_g_funext_x_judgement,
            h_x_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_B_f_g_h_funext_h_happly_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            A_Ux_judgement,
            Ux_A_B_f_g_h_x_happly_funext_h_x_judgement,
        }, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_B_f_g_funext_h_happly_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            homotopy_Ux_A_B_f_g__Ux_judgement,
            Ux_A_B_f_g_h_funext_h_happly_judgement,
        }, 2, 0, (tt_id[]){h_homotopy_A_B_f_g_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_B_f_funext_h_happly_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            pi_x_A_B_x__Ux_judgement,
            Ux_A_B_f_g_funext_h_happly_judgement,
        }, 2, 0, (tt_id[]){g__pi_x_A_B_x_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_B_funext_h_happly_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            pi_x_A_B_x__Ux_judgement,
            Ux_A_B_f_funext_h_happly_judgement,
        }, 2, 0, (tt_id[]){f__pi_x_A_B_x_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_funext_h_happly_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            pi_A_Ux__UUOmega_judgement,
            Ux_A_B_funext_h_happly_judgement,
        }, 2, 0, (tt_id[]){B__pi_A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id Ux_funext_h_happly_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            Ux_UUOmega_judgement,
            Ux_A_funext_h_happly_judgement,
        }, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id funext_h_happly_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            UUOmega_UUKappa_judgement,
            Ux_funext_h_happly_judgement,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id funext_compute_axiom = proof_step(e, TT_Axiom, (tt_id[]){funext_h_happly_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id p_eq_pi_x_A_B_x__f__g_context = proof_step(e, TT_CtxExt, (tt_id[]){eq_pi_x_A_B_x__f__g__Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id p_eq_pi_x_A_B_x__f__g_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, p_eq_pi_x_A_B_x__f__g_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id haply_Ux_A_B_f_g_p_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            happly_Ux_A_B_f_g_judgement,
            p_eq_pi_x_A_B_x__f__g_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id reduced_haply_Ux_A_B_f_g_p_judgement = proof_step(e, TT_Subs, (tt_id[]){haply_Ux_A_B_f_g_p_judgement, defeq_homotopy}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    reduced_haply_Ux_A_B_f_g_p_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){reduced_haply_Ux_A_B_f_g_p_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id haply_Ux_A_B_f_g_p_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            reduced_haply_Ux_A_B_f_g_p_judgement,
            x_A_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_x_happly_p_x_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, haply_Ux_A_B_f_g_p_x_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id lam_x_happly_p_x_homotopy_judgement = proof_step(e, TT_Subs, (tt_id[]){
            lam_x_happly_p_x_judgement,
            homotopy_Ux_A_B_f_g_eval_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_happly_p_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            funext_Ux_A_B_f_g_judgement,
            lam_x_happly_p_x_homotopy_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_pi_x_A_B_x__f_g__p__funext_happly_p__Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){
                eq_pi_x_A_B_x__f__g__Ux_judgement,
                p_eq_pi_x_A_B_x__f__g_judgement,
                funext_happly_p_judgement,
            }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_B_f_g_funext_unique_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            eq_pi_x_A_B_x__f__g__Ux_judgement,
            eq_pi_x_A_B_x__f_g__p__funext_happly_p__Ux_judgement,
        }, 2, 0, (tt_id[]){p_eq_pi_x_A_B_x__f__g_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_B_f_funext_unique_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            pi_x_A_B_x__Ux_judgement,
            Ux_A_B_f_g_funext_unique_judgement,
        }, 2, 0, (tt_id[]){g__pi_x_A_B_x_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_B_funext_unique_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            pi_x_A_B_x__Ux_judgement,
            Ux_A_B_f_funext_unique_judgement,
        }, 2, 0, (tt_id[]){f__pi_x_A_B_x_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_funext_unique_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            pi_A_Ux__UUOmega_judgement,
            Ux_A_B_funext_unique_judgement,
        }, 2, 0, (tt_id[]){B__pi_A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id Ux_funexy_unique_type_judgement = proof_step(e, TT_PiForm, (tt_id[]){Ux_UUOmega_judgement, Ux_A_funext_unique_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id funext_unique_type_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            UUOmega_UUKappa_judgement,
            Ux_funexy_unique_type_judgement,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id funext_unique_axiom = proof_step(e, TT_Axiom, (tt_id[]){funext_unique_type_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_isequiv, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){isequiv_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Ux_A_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){isequiv_Ux_A_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Ux_A_A_id_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){isequiv_Ux_A_A_judgement, id_Ux_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id refl_isequiv_id_A_judgement = proof_step(e, TT_DefEqRefl, (tt_id[]){isequiv_Ux_A_A_id_Ux_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_isequiv_id_A_judgement = proof_step(e, TT_HighExp, (tt_id[]){refl_isequiv_id_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_isequiv_id_A_judgement = proof_step(e, TT_High0, (tt_id[]){refl_isequiv_id_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_isequiv_id_A_judgement = proof_step(e, TT_HighSubs, (tt_id[]){refl_isequiv_id_A_judgement, id_defeq_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_isequiv_id_A_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){refl_isequiv_id_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_isequiv_id_A_judgement = proof_step(e, TT_HighSubs, (tt_id[]){
            refl_isequiv_id_A_judgement,
            isequiv_defeq_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_isequiv_id_A_judgement = proof_step(e, TT_HighSubs, (tt_id[]){refl_isequiv_id_A_judgement, id_defeq_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_5=0; loop_5<3; ++loop_5) {
    refl_isequiv_id_A_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){refl_isequiv_id_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    refl_isequiv_id_A_judgement = proof_step(e, TT_HighSubs, (tt_id[]){refl_isequiv_id_A_judgement, defeq_homotopy}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_6=0; loop_6<3; ++loop_6) {
    refl_isequiv_id_A_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){refl_isequiv_id_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    refl_isequiv_id_A_judgement = proof_step(e, TT_HighSubs, (tt_id[]){refl_isequiv_id_A_judgement, id_defeq_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_isequiv_id_A_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){refl_isequiv_id_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_isequiv_id_A_judgement = proof_step(e, TT_HighSubs, (tt_id[]){refl_isequiv_id_A_judgement, ap_defeq_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_7=0; loop_7<5; ++loop_7) {
    refl_isequiv_id_A_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){refl_isequiv_id_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id pi_A_A_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id g_pi_A_A_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_A_A_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id g_pi_A_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, g_pi_A_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id g_x__A_judgement = proof_step(e, TT_PiElim, (tt_id[]){g_pi_A_A_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_A_g_x_x__Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){
            A_Ux_judgement,
            g_x__A_judgement,
            x_A_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_x__eq_A_g_x_x_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, eq_A_g_x_x__Ux_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id id_isequiv_eta_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_x__eq_A_g_x_x_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id id_isequiv_eta_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, id_isequiv_eta_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_isequiv_epsilon_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_x__eq_A_g_x_x_Ux_judgement}, 1, 0, (tt_id[]){id_isequiv_eta_context}, 1, __FILE__, __LINE__);
    tt_id id_isequiv_epsilon_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, id_isequiv_epsilon_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ap_Ux_A_A = proof_step(e, TT_PiElim, (tt_id[]){ap_Ux_A_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ap_Ux_A_A_id = proof_step(e, TT_PiElim, (tt_id[]){ap_Ux_A_A, id_Ux_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ap_Ux_A_A_id_gx = proof_step(e, TT_PiElim, (tt_id[]){ap_Ux_A_A_id, g_x__A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ap_Ux_A_A_id_gx_x = proof_step(e, TT_PiElim, (tt_id[]){ap_Ux_A_A_id_gx, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_isequiv_eta_x = proof_step(e, TT_PiElim, (tt_id[]){id_isequiv_eta_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    ap_Ux_A_A_id_gx_x = proof_step(e, TT_PiElim, (tt_id[]){ap_Ux_A_A_id_gx_x, id_isequiv_eta_x}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_isequiv_rhs_inner = proof_step(e, TT_Subs, (tt_id[]){ap_Ux_A_A_id_gx_x, id_defeq_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    id_isequiv_rhs_inner = proof_step(e, TT_Subs, (tt_id[]){id_isequiv_rhs_inner, ap_defeq_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_8=0; loop_8<2; ++loop_8) {
    id_isequiv_rhs_inner = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){id_isequiv_rhs_inner}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id id_isequiv_epsilon_x = proof_step(e, TT_PiElim, (tt_id[]){id_isequiv_epsilon_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id x_inner_equality_for_isequiv = proof_step(e, TT_EqForm, (tt_id[]){
            eq_A_g_x_x__Ux_judgement,
            id_isequiv_rhs_inner,
            id_isequiv_epsilon_x,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id inner_equality_for_isequiv = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, x_inner_equality_for_isequiv}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id lam_epsilon_inner_isequiv_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_x__eq_A_g_x_x_Ux_judgement,
            inner_equality_for_isequiv,
        }, 2, 0, (tt_id[]){id_isequiv_epsilon_context}, 1, __FILE__, __LINE__);
    tt_id lam_eta_lam_epsilon_inner_isequiv_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_x__eq_A_g_x_x_Ux_judgement,
            lam_epsilon_inner_isequiv_judgement,
        }, 2, 0, (tt_id[]){id_isequiv_eta_context}, 1, __FILE__, __LINE__);
    tt_id lam_g_lam_eta_lam_epsilon_inner_isequiv_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
                pi_A_A_Ux_judgement,
                lam_eta_lam_epsilon_inner_isequiv_judgement,
            }, 2, 0, (tt_id[]){g_pi_A_A_context}, 1, __FILE__, __LINE__);
    tt_id lam_eta_lam_epsilon_fixed_g_eq_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            lam_g_lam_eta_lam_epsilon_inner_isequiv_judgement,
            id_Ux_A_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id refl_x_judgement = proof_step(e, TT_EqIntro, (tt_id[]){x_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_Ux_A_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){id_Ux_A_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id defeq_x_id_Ux_A_x_judgement = proof_step(e, TT_DefEqRefl, (tt_id[]){id_Ux_A_x_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    defeq_x_id_Ux_A_x_judgement = proof_step(e, TT_HighExp, (tt_id[]){defeq_x_id_Ux_A_x_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    defeq_x_id_Ux_A_x_judgement = proof_step(e, TT_High0, (tt_id[]){defeq_x_id_Ux_A_x_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    defeq_x_id_Ux_A_x_judgement = proof_step(e, TT_HighSubs, (tt_id[]){defeq_x_id_Ux_A_x_judgement, id_defeq_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    defeq_x_id_Ux_A_x_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){defeq_x_id_Ux_A_x_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id refl_x_eq_A_id_Ux_A_x_x_judgement = proof_step(e, TT_HighType, (tt_id[]){refl_x_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_x_eq_A_id_Ux_A_x_x_judgement = proof_step(e, TT_High1, (tt_id[]){refl_x_eq_A_id_Ux_A_x_x_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    refl_x_eq_A_id_Ux_A_x_x_judgement = proof_step(e, TT_HighSubs, (tt_id[]){
            refl_x_eq_A_id_Ux_A_x_x_judgement,
            defeq_x_id_Ux_A_x_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_x_refl_x__pi_x_eq_A_id_x_x_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, refl_x_eq_A_id_Ux_A_x_x_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id lam_eta_lam_epsilon_fixed_g_eta_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            lam_eta_lam_epsilon_fixed_g_eq_judgement,
            lam_x_refl_x__pi_x_eq_A_id_x_x_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_g_sigma_epsilon_type_template_judgement = proof_step(e, TT_PiIntro, (tt_id[]){pi_A_A_Ux_judgement, pi_x__eq_A_g_x_x_Ux_judgement}, 2, 0, (tt_id[]){g_pi_A_A_context}, 1, __FILE__, __LINE__);
    tt_id sigma_epsilon_type_template_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            lam_g_sigma_epsilon_type_template_judgement,
            id_Ux_A_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    sigma_epsilon_type_template_judgement = proof_step(e, TT_HighExp, (tt_id[]){sigma_epsilon_type_template_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    sigma_epsilon_type_template_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){sigma_epsilon_type_template_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id template_eta_context = proof_step(e, TT_CtxExt, (tt_id[]){sigma_epsilon_type_template_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id template_eta_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, template_eta_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id template_epsilon_context = proof_step(e, TT_CtxExt, (tt_id[]){sigma_epsilon_type_template_judgement}, 1, 0, (tt_id[]){template_eta_context}, 1, __FILE__, __LINE__);
    tt_id template_epsilon_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, template_epsilon_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement = proof_step(e, TT_PiElim, (tt_id[]){
                lam_eta_lam_epsilon_fixed_g_eta_judgement,
                lam_x_refl_x__pi_x_eq_A_id_x_x_judgement,
            }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id reduced_lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement = proof_step(e, TT_HighExp, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    reduced_lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement = proof_step(e, TT_High0, (tt_id[]){reduced_lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    reduced_lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement = proof_step(e, TT_High0, (tt_id[]){reduced_lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned i=0; i<3; ++i) {
    reduced_lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){reduced_lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    if (i < 2) {
    reduced_lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement = proof_step(e, TT_HighUp, (tt_id[]){reduced_lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
}
    tt_id reduced_inner_expression = proof_step(e, TT_DefEqRefl, (tt_id[]){reduced_lam_eta_lam_epsilon_fixed_g_eta_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    reduced_inner_expression = proof_step(e, TT_HighExp, (tt_id[]){reduced_inner_expression}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    reduced_inner_expression = proof_step(e, TT_High0, (tt_id[]){reduced_inner_expression}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    reduced_inner_expression = proof_step(e, TT_HighSubs, (tt_id[]){reduced_inner_expression, id_defeq_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_10=0; loop_10<2; ++loop_10) {
    reduced_inner_expression = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){reduced_inner_expression}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id refl_refl_x_judgement = proof_step(e, TT_EqIntro, (tt_id[]){refl_x_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_x_refl_refl_x_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, refl_refl_x_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_PiElim, (tt_id[]){
                lam_eta_lam_epsilon_fixed_g_eta_judgement,
                lam_x_refl_x__pi_x_eq_A_id_x_x_judgement,
            }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_HighExp, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_High0, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_High0, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_HighUp, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_HighUp, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_DefEqRefl, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_HighExp, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_High0, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_HighSubs, (tt_id[]){
                lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement,
                id_defeq_judgement,
            }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id first_witness = proof_step(e, TT_Subs, (tt_id[]){
            lam_x_refl_refl_x_judgement,
            lam_eta_lam_epsilon_fixed_g_eta_var_epsilon_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id sigma_epsilon_fix_g_type_template_judgement = proof_step(e, TT_PiElim, (tt_id[]){
                lam_eta_lam_epsilon_fixed_g_eta_judgement,
                template_epsilon_judgement,
            }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    sigma_epsilon_fix_g_type_template_judgement = proof_step(e, TT_HighExp, (tt_id[]){sigma_epsilon_fix_g_type_template_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    sigma_epsilon_fix_g_type_template_judgement = proof_step(e, TT_High0, (tt_id[]){sigma_epsilon_fix_g_type_template_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    sigma_epsilon_fix_g_type_template_judgement = proof_step(e, TT_High0, (tt_id[]){sigma_epsilon_fix_g_type_template_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned i=0; i<3; ++i) {
    sigma_epsilon_fix_g_type_template_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){sigma_epsilon_fix_g_type_template_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    if (i < 2) {
    sigma_epsilon_fix_g_type_template_judgement = proof_step(e, TT_HighUp, (tt_id[]){sigma_epsilon_fix_g_type_template_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
}
    tt_id lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement = proof_step(e, TT_PiElim, (tt_id[]){
                lam_eta_lam_epsilon_fixed_g_eta_judgement,
                template_epsilon_judgement,
            }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement = proof_step(e, TT_HighExp, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement = proof_step(e, TT_High0, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement = proof_step(e, TT_High0, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement = proof_step(e, TT_HighUp, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement = proof_step(e, TT_HighUp, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id sigma_epsilon_witness = proof_step(e, TT_SigmaIntro, (tt_id[]){
            lam_x_refl_x__pi_x_eq_A_id_x_x_judgement,
            lam_eta_lam_epsilon_fixed_g_eta_epsilontemplate_judgement,
            first_witness,
        }, 3, 0, (tt_id[]){template_epsilon_context}, 1, __FILE__, __LINE__);
    tt_id eta_epsilon_template_type_1_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            lam_eta_lam_epsilon_fixed_g_eq_judgement,
            template_eta_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eta_epsilon_template_type_2_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            eta_epsilon_template_type_1_judgement,
            template_epsilon_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    eta_epsilon_template_type_2_judgement = proof_step(e, TT_HighExp, (tt_id[]){eta_epsilon_template_type_2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    eta_epsilon_template_type_2_judgement = proof_step(e, TT_High0, (tt_id[]){eta_epsilon_template_type_2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    eta_epsilon_template_type_2_judgement = proof_step(e, TT_High0, (tt_id[]){eta_epsilon_template_type_2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    eta_epsilon_template_type_2_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){eta_epsilon_template_type_2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    eta_epsilon_template_type_2_judgement = proof_step(e, TT_HighUp, (tt_id[]){eta_epsilon_template_type_2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    eta_epsilon_template_type_2_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){eta_epsilon_template_type_2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    eta_epsilon_template_type_2_judgement = proof_step(e, TT_HighUp, (tt_id[]){eta_epsilon_template_type_2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    eta_epsilon_template_type_2_judgement = proof_step(e, TT_BetaReducePointed, (tt_id[]){eta_epsilon_template_type_2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eta_sigma_epsilon_template_type_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){
            sigma_epsilon_type_template_judgement,
            eta_epsilon_template_type_2_judgement,
        }, 2, 0, (tt_id[]){template_epsilon_context}, 1, __FILE__, __LINE__);
    tt_id sigma_eta_witness = proof_step(e, TT_SigmaIntro, (tt_id[]){
            lam_x_refl_x__pi_x_eq_A_id_x_x_judgement,
            eta_sigma_epsilon_template_type_judgement,
            sigma_epsilon_witness,
        }, 3, 0, (tt_id[]){template_eta_context}, 1, __FILE__, __LINE__);
    tt_id inner_equality_for_isequiv_fix_epsilon_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){
                pi_x__eq_A_g_x_x_Ux_judgement,
                inner_equality_for_isequiv,
            }, 2, 0, (tt_id[]){id_isequiv_epsilon_context}, 1, __FILE__, __LINE__);
    inner_equality_for_isequiv_fix_epsilon_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){
                pi_x__eq_A_g_x_x_Ux_judgement,
                inner_equality_for_isequiv_fix_epsilon_judgement,
            }, 2, 0, (tt_id[]){id_isequiv_eta_context}, 1, __FILE__, __LINE__);
    tt_id id_isequiv_witness_judgement = proof_step(e, TT_SigmaIntro, (tt_id[]){
            id_Ux_A_judgement,
            inner_equality_for_isequiv_fix_epsilon_judgement,
            sigma_eta_witness,
        }, 3, 0, (tt_id[]){g_pi_A_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_id_isequiv_proof = proof_step(e, TT_Subs, (tt_id[]){
            id_isequiv_witness_judgement,
            refl_isequiv_id_A_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_id_isequiv_proof = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_id_isequiv_proof}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id id_isequiv_proof = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_id_isequiv_proof}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id id_isequiv_defeq = proof_step(e, TT_Def, (tt_id[]){id_isequiv_proof}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_id_isequiv = proof_step(e, TT_DefEqExtL, (tt_id[]){id_isequiv_defeq}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Ux_A_C_judgement = proof_step(e, TT_PiElim, (tt_id[]){isequiv_Ux_A_judgement, C_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    isequiv_Ux_A_C_judgement = proof_step(e, TT_PiElim, (tt_id[]){isequiv_Ux_A_C_judgement, f_pi_A_C_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_C_areequiv_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){pi_A_C__Ux_judgement, isequiv_Ux_A_C_judgement}, 2, 0, (tt_id[]){f_pi_A_C_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_areequiv_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_C_areequiv_judgement}, 2, 0, (tt_id[]){C_Ux_context}, 1, __FILE__, __LINE__);
    tt_id Ux_areequiv_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_areequiv_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id areequiv_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_areequiv_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id areequiv_defeq_judgement = proof_step(e, TT_Def, (tt_id[]){areequiv_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_areequiv = proof_step(e, TT_DefEqExtL, (tt_id[]){areequiv_defeq_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id R_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id R_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, R_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id S_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){R_Ux_context}, 1, __FILE__, __LINE__);
    tt_id S_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, S_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_Ux_R_S__UUOmega_judgement = proof_step(e, TT_EqForm, (tt_id[]){
            Ux_UUOmega_judgement,
            R_Ux_judgement,
            S_Ux_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id p_eq_Ux_R_S_context = proof_step(e, TT_CtxExt, (tt_id[]){eq_Ux_R_S__UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id p_eq_Ux_R_S__Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, p_eq_Ux_R_S_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id areequiv_Ux__pi_Ux_pi_Ux_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_areequiv, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id areequiv_Ux_R__pi_Ux_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            areequiv_Ux__pi_Ux_pi_Ux_Ux_judgement,
            R_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id areequiv_Ux_R_S__Ux_judegement = proof_step(e, TT_PiElim, (tt_id[]){areequiv_Ux_R__pi_Ux_Ux_judgement, S_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id areequiv_Ux_R_R__Ux_judegement = proof_step(e, TT_PiElim, (tt_id[]){areequiv_Ux_R__pi_Ux_Ux_judgement, R_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id reduced_areequiv_Ux_R_R__Uy_judegement = proof_step(e, TT_DefEqRefl, (tt_id[]){areequiv_Ux_R_R__Ux_judegement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    reduced_areequiv_Ux_R_R__Uy_judegement = proof_step(e, TT_HighExp, (tt_id[]){reduced_areequiv_Ux_R_R__Uy_judegement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    reduced_areequiv_Ux_R_R__Uy_judegement = proof_step(e, TT_High0, (tt_id[]){reduced_areequiv_Ux_R_R__Uy_judegement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    reduced_areequiv_Ux_R_R__Uy_judegement = proof_step(e, TT_HighSubs, (tt_id[]){
            reduced_areequiv_Ux_R_R__Uy_judegement,
            areequiv_defeq_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_12=0; loop_12<3; ++loop_12) {
    reduced_areequiv_Ux_R_R__Uy_judegement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){reduced_areequiv_Ux_R_R__Uy_judegement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id id_Ux__pi_A_pi_A_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_id, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_Ux_R__pi_A_pi_A_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){id_Ux__pi_A_pi_A_A_judgement, R_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_isequiv_Ux__pi_A_isequiv_Ux_A_A_id_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_id_isequiv, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_isequiv_Ux__pi_A_isequiv_Uy_A_A_id_Ux_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){
                id_isequiv_Ux__pi_A_isequiv_Ux_A_A_id_Ux_A_judgement,
                R_Ux_judgement,
            }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_R_R__Uy_judgement = proof_step(e, TT_PiForm, (tt_id[]){R_Ux_judgement, R_Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id g_pi_R_R_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_R_R__Uy_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id g_pi_R_R_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, g_pi_R_R_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Ux__pi_A_pi_C_pi_A_C__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_isequiv, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Ux_R__pi_C_pi_R_C__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            isequiv_Ux__pi_A_pi_C_pi_A_C__Ux_judgement,
            R_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Ux_R__pi_R_R__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            isequiv_Ux_R__pi_C_pi_R_C__Ux_judgement,
            R_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Ux_R__pi_R_R_g__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            isequiv_Ux_R__pi_R_R__Ux_judgement,
            g_pi_R_R_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id R_isequiv_R_judgement = proof_step(e, TT_SigmaIntro, (tt_id[]){
            id_Ux_R__pi_A_pi_A_A_judgement,
            isequiv_Ux_R__pi_R_R_g__Ux_judgement,
            id_isequiv_Ux__pi_A_isequiv_Uy_A_A_id_Ux_A_judgement,
        }, 3, 0, (tt_id[]){g_pi_R_R_context}, 1, __FILE__, __LINE__);
    tt_id areequiv_R_R_judgement = proof_step(e, TT_Subs, (tt_id[]){
            R_isequiv_R_judgement,
            reduced_areequiv_Ux_R_R__Uy_judegement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id areequiv_Ux_R_S_p_judgement = proof_step(e, TT_EqElim, (tt_id[]){
            areequiv_Ux_R_S__Ux_judegement,
            areequiv_R_R_judgement,
            R_Ux_judgement,
            S_Ux_judgement,
            p_eq_Ux_R_S__Ux_judgement,
        }, 5, 0, (tt_id[]){
            R_Ux_context,
            S_Ux_context,
            0,
            R_Ux_context,
        }, 4, __FILE__, __LINE__);
    tt_id areequiv_Ux_R_S_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            eq_Ux_R_S__UUOmega_judgement,
            areequiv_Ux_R_S_p_judgement,
        }, 2, 0, (tt_id[]){p_eq_Ux_R_S_context}, 1, __FILE__, __LINE__);
    tt_id areequiv_Ux_R_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, areequiv_Ux_R_S_judgement}, 2, 0, (tt_id[]){S_Ux_context}, 1, __FILE__, __LINE__);
    tt_id areequiv_Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, areequiv_Ux_R_judgement}, 2, 0, (tt_id[]){R_Ux_context}, 1, __FILE__, __LINE__);
    areequiv_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, areequiv_Ux_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id defeq_uEqAreEquiv_judgement = proof_step(e, TT_Def, (tt_id[]){areequiv_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_ueqequiv = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_uEqAreEquiv_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_R_S_univalence_type_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            areequiv_Ux_R_S__Ux_judegement,
            eq_Ux_R_S__UUOmega_judgement,
        }, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_R_univalence_type_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            Ux_UUOmega_judgement,
            Ux_R_S_univalence_type_judgement,
        }, 2, 0, (tt_id[]){S_Ux_context}, 1, __FILE__, __LINE__);
    tt_id Ux_univalence_type_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            Ux_UUOmega_judgement,
            Ux_R_univalence_type_judgement,
        }, 2, 0, (tt_id[]){R_Ux_context}, 1, __FILE__, __LINE__);
    tt_id univalence_type_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            UUOmega_UUKappa_judgement,
            Ux_univalence_type_judgement,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id univalence_axiom = proof_step(e, TT_Axiom, (tt_id[]){univalence_type_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id B_y__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){B__pi_A_Ux_judgement, y_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi__B_x__B_y__Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){B_x__Ux_judgement, B_y__Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id id__B_x__B_x__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){id_Ux_judgement, B_x__Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_B_x_y_p_transport_judgement = proof_step(e, TT_EqElim, (tt_id[]){
            pi__B_x__B_y__Ux_judgement,
            id__B_x__B_x__Ux_judgement,
            x_A_judgement,
            y_A_judgement,
            p_eq_A_x_y_judgement,
        }, 5, 0, (tt_id[]){
            x_A_context,
            y_A_context,
            0,
            x_A_context,
        }, 4, __FILE__, __LINE__);
    tt_id Ux_A_B_x_y_transport_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            eq_A_x_y__Ux_judgement,
            Ux_A_B_x_y_p_transport_judgement,
        }, 2, 0, (tt_id[]){p_eq_A_x_y_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_B_x_transport_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_B_x_y_transport_judgement}, 2, 0, (tt_id[]){y_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_B_transport_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_Ux_judgement, Ux_A_B_x_transport_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_transport_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_A_Ux__UUOmega_judgement,
            Ux_A_B_transport_judgement,
        }, 2, 0, (tt_id[]){B__pi_A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id Ux_transport_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_transport_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id transport_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_transport_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id transport_defeq_judgement = proof_step(e, TT_Def, (tt_id[]){transport_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_transport = proof_step(e, TT_DefEqExtL, (tt_id[]){transport_defeq_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Uy_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Uy_Ux_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Uy_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_Ux_Uy_judgement = proof_step(e, TT_PiElim, (tt_id[]){id_Ux_judgement, Uy_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id transport_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_transport, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id transport_Ux_Uy_judgement = proof_step(e, TT_PiElim, (tt_id[]){transport_Ux_judgement, Uy_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Uy_context = proof_step(e, TT_CtxExt, (tt_id[]){Uy_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Uy_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Uy_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_Ux_Uy_A_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){id_Ux_Uy_judgement, A_Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_Ux_Uy_A__is_Ux_judgement = proof_step(e, TT_UCumulContext, (tt_id[]){id_Ux_Uy_A_Ux_judgement, Uy_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id id_Ux_Uy__is_Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Uy_Ux_judgement, id_Ux_Uy_A__is_Ux_judgement}, 2, 0, (tt_id[]){A_Uy_context}, 1, __FILE__, __LINE__);
    tt_id transport_Ux_Uy_id_Ux_Uy_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            transport_Ux_Uy_judgement,
            id_Ux_Uy__is_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id B_Uy_context = proof_step(e, TT_CtxExt, (tt_id[]){Uy_Ux_judgement}, 1, 0, (tt_id[]){A_Uy_context}, 1, __FILE__, __LINE__);
    tt_id B_Uy_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, B_Uy_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Uy_UUOmega_judgement = proof_step(e, TT_UCumulOmega, (tt_id[]){Uy_Ux_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id areequiv_Uy_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_areequiv, Uy_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id areequiv_Uy_A_Uy_judgement = proof_step(e, TT_PiElim, (tt_id[]){areequiv_Uy_judgement, A_Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id areequiv_Uy_A_B__Uy_judgement = proof_step(e, TT_PiElim, (tt_id[]){areequiv_Uy_A_Uy_judgement, B_Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id e_areequiv_Uy_A_Uy_B_Uy_context = proof_step(e, TT_CtxExt, (tt_id[]){areequiv_Uy_A_B__Uy_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id e_areequiv_Uy_A_Uy_B_Uy_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, e_areequiv_Uy_A_Uy_B_Uy_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ua_Uy_judgement = proof_step(e, TT_PiElim, (tt_id[]){univalence_axiom, Uy_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ua_Uy_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){ua_Uy_judgement, A_Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ua_Uy_A_B_judgement = proof_step(e, TT_PiElim, (tt_id[]){ua_Uy_A_judgement, B_Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ua_Uy_A_B_e_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            ua_Uy_A_B_judgement,
            e_areequiv_Uy_A_Uy_B_Uy_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id transport_Ux_Uy_id_Ux_Uy_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){transport_Ux_Uy_id_Ux_Uy_judgement, A_Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id transport_Ux_Uy_id_Ux_Uy_A_B_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            transport_Ux_Uy_id_Ux_Uy_A_judgement,
            B_Uy_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id transport_Ux_Uy_id_Ux_Uy_A_B_ua_Uy_A_B_e_judgement = proof_step(e, TT_PiElim, (tt_id[]){
                transport_Ux_Uy_id_Ux_Uy_A_B_judgement,
                ua_Uy_A_B_e_judgement,
            }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    transport_Ux_Uy_id_Ux_Uy_A_B_ua_Uy_A_B_e_judgement = proof_step(e, TT_Subs, (tt_id[]){
            transport_Ux_Uy_id_Ux_Uy_A_B_ua_Uy_A_B_e_judgement,
            transport_defeq_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    transport_Ux_Uy_id_Ux_Uy_A_B_ua_Uy_A_B_e_judgement = proof_step(e, TT_Subs, (tt_id[]){
            transport_Ux_Uy_id_Ux_Uy_A_B_ua_Uy_A_B_e_judgement,
            id_defeq_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_13=0; loop_13<3; ++loop_13) {
    transport_Ux_Uy_id_Ux_Uy_A_B_ua_Uy_A_B_e_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){transport_Ux_Uy_id_Ux_Uy_A_B_ua_Uy_A_B_e_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id e_isequiv_judgement = proof_step(e, TT_Subs, (tt_id[]){
            e_areequiv_Uy_A_Uy_B_Uy_judgement,
            areequiv_defeq_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_14=0; loop_14<3; ++loop_14) {
    e_isequiv_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){e_isequiv_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id pr1_Uy_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_pr1, Uy_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_A_B__Uy_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Uy_judgement, B_Uy_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id pr1_Uy_pi_A_B_judgement = proof_step(e, TT_PiElim, (tt_id[]){pr1_Uy_judgement, pi_A_B__Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Uy = proof_step(e, TT_PiElim, (tt_id[]){def_isequiv, Uy_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Uy_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){isequiv_Uy, A_Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id isequiv_Uy_A_B = proof_step(e, TT_PiElim, (tt_id[]){isequiv_Uy_A_judgement, B_Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr1_Uy_pi_A_B_isequiv_judgement = proof_step(e, TT_PiElim, (tt_id[]){pr1_Uy_pi_A_B_judgement, isequiv_Uy_A_B}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_equivalence_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            pr1_Uy_pi_A_B_isequiv_judgement,
            e_isequiv_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    f_equivalence_judgement = proof_step(e, TT_HighExp, (tt_id[]){f_equivalence_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_15=0; loop_15<4; ++loop_15) {
    f_equivalence_judgement = proof_step(e, TT_High0, (tt_id[]){f_equivalence_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id pr1_defeq_judgement = proof_step(e, TT_DefLookup, (tt_id[]){f_equivalence_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    f_equivalence_judgement = proof_step(e, TT_UnHigh, (tt_id[]){f_equivalence_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    f_equivalence_judgement = proof_step(e, TT_Subs, (tt_id[]){f_equivalence_judgement, pr1_defeq_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_16=0; loop_16<3; ++loop_16) {
    f_equivalence_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){f_equivalence_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id x_A_Uy__context = proof_step(e, TT_CtxExt, (tt_id[]){A_Uy_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id x_A_Uy_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, x_A_Uy__context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id transport_ua_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            transport_Ux_Uy_id_Ux_Uy_A_B_ua_Uy_A_B_e_judgement,
            x_A_Uy_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_equiv_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){f_equivalence_judgement, x_A_Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_Uy_A_B_e_x__eq_B__transport_ua_x__f_equiv_x__Uy_judgement = proof_step(e, TT_EqForm, (tt_id[]){
                B_Uy_judgement,
                transport_ua_x_judgement,
                f_equiv_x_judgement,
            }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_Uy_A_B_e__eq_B__transport_ua_x__f_equiv_x__Uy_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                A_Uy_judgement,
                Ux_Uy_A_B_e_x__eq_B__transport_ua_x__f_equiv_x__Uy_judgement,
            }, 2, 0, (tt_id[]){x_A_Uy__context}, 1, __FILE__, __LINE__);
    tt_id Ux_Uy_A_B__eq_B__transport_ua_x__f_equiv_x__Uy_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                areequiv_Uy_A_B__Uy_judgement,
                Ux_Uy_A_B_e__eq_B__transport_ua_x__f_equiv_x__Uy_judgement,
            }, 2, 0, (tt_id[]){e_areequiv_Uy_A_Uy_B_Uy_context}, 1, __FILE__, __LINE__);
    tt_id Ux_Uy_A__eq_B__transport_ua_x__f_equiv_x__Uy_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                Uy_Ux_judgement,
                Ux_Uy_A_B__eq_B__transport_ua_x__f_equiv_x__Uy_judgement,
            }, 2, 0, (tt_id[]){B_Uy_context}, 1, __FILE__, __LINE__);
    tt_id Ux_Uy__eq_B__transport_ua_x__f_equiv_x__Uy_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                Uy_Ux_judgement,
                Ux_Uy_A__eq_B__transport_ua_x__f_equiv_x__Uy_judgement,
            }, 2, 0, (tt_id[]){A_Uy_context}, 1, __FILE__, __LINE__);
    tt_id Ux__eq_B__transport_ua_x__f_equiv_x__Uy_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                Ux_UUOmega_judgement,
                Ux_Uy__eq_B__transport_ua_x__f_equiv_x__Uy_judgement,
            }, 2, 0, (tt_id[]){Uy_Ux_context}, 1, __FILE__, __LINE__);
    tt_id transport_ua_x__f_equiv_x__Uy_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            UUOmega_UUKappa_judgement,
            Ux__eq_B__transport_ua_x__f_equiv_x__Uy_judgement,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id ua_elim_axiom = proof_step(e, TT_Axiom, (tt_id[]){transport_ua_x__f_equiv_x__Uy_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_Uy_A_B__Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){
            Uy_Ux_judgement,
            A_Uy_judgement,
            B_Uy_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id p_eq_Uy_A_B_context = proof_step(e, TT_CtxExt, (tt_id[]){eq_Uy_A_B__Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id p_eq_Uy_A_B_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, p_eq_Uy_A_B_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ueqequiv_Uy_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_ueqequiv, Uy_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ueqequiv_Uy_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){ueqequiv_Uy_judgement, A_Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ueqequiv_Uy_A_B_judgement = proof_step(e, TT_PiElim, (tt_id[]){ueqequiv_Uy_A_judgement, B_Uy_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ueqequiv_Uy_A_B_p_judgement = proof_step(e, TT_PiElim, (tt_id[]){ueqequiv_Uy_A_B_judgement, p_eq_Uy_A_B_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ua_ueqequiv_judgement = proof_step(e, TT_PiElim, (tt_id[]){ua_Uy_A_B_judgement, ueqequiv_Uy_A_B_p_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq__eq_Uy_A_B__p___ua_Uy_A_B__ueqareequiv_Uy_A_B_p_judgement = proof_step(e, TT_EqForm, (tt_id[]){
                eq_Uy_A_B__Ux_judgement,
                p_eq_Uy_A_B_judgement,
                ua_ueqequiv_judgement,
            }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_Uy_A_B_ua_uniq_expression = proof_step(e, TT_PiForm, (tt_id[]){
            eq_Uy_A_B__Ux_judgement,
            eq__eq_Uy_A_B__p___ua_Uy_A_B__ueqareequiv_Uy_A_B_p_judgement,
        }, 2, 0, (tt_id[]){p_eq_Uy_A_B_context}, 1, __FILE__, __LINE__);
    tt_id Ux_Uy_A_ua_uniq_expression = proof_step(e, TT_PiForm, (tt_id[]){Uy_Ux_judgement, Ux_Uy_A_B_ua_uniq_expression}, 2, 0, (tt_id[]){B_Uy_context}, 1, __FILE__, __LINE__);
    tt_id Ux_Uy_ua_uniq_expression = proof_step(e, TT_PiForm, (tt_id[]){Uy_Ux_judgement, Ux_Uy_A_ua_uniq_expression}, 2, 0, (tt_id[]){A_Uy_context}, 1, __FILE__, __LINE__);
    tt_id Ux_ua_uniq_expression = proof_step(e, TT_PiForm, (tt_id[]){Ux_UUOmega_judgement, Ux_Uy_ua_uniq_expression}, 2, 0, (tt_id[]){Uy_Ux_context}, 1, __FILE__, __LINE__);
    tt_id ua_uniq_expression = proof_step(e, TT_PiForm, (tt_id[]){UUOmega_UUKappa_judgement, Ux_ua_uniq_expression}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id ua_unique_axiom = proof_step(e, TT_Axiom, (tt_id[]){ua_uniq_expression}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return (proof_tuple){{def_homotopy, def_happly, def_ap, def_id, def_isequiv, funext_axiom, funext_compute_axiom, funext_unique_axiom, def_id_isequiv, def_ueqequiv, univalence_axiom, def_transport, ua_elim_axiom, ua_unique_axiom}};
}

tt_id p_define_is_decidable(tt_engine *e) {
    tt_id not_judgement = p_define_not(e);
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Not_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){not_judgement, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Not_Ux_A_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){Not_Ux_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id plus_A_Not_Ux_A__Ux_judgement = proof_step(e, TT_SumForm, (tt_id[]){A_Ux_judgement, Not_Ux_A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_A_plus_A_Not_Ux_A__Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            Ux_UUOmega_judgement,
            plus_A_Not_Ux_A__Ux_judgement,
        }, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id lam_Ux_lam_A_plus_A_Not_Ux_A__Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            UUOmega_UUKappa_judgement,
            lam_A_plus_A_Not_Ux_A__Ux_judgement,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id isDecidable_defeq = proof_step(e, TT_Def, (tt_id[]){lam_Ux_lam_A_plus_A_Not_Ux_A__Ux_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return proof_step(e, TT_DefEqExtL, (tt_id[]){isDecidable_defeq}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

tt_id p_define_is_set(tt_engine *e) {
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id a_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id b_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){a_A_context}, 1, __FILE__, __LINE__);
    tt_id a_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, a_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id b_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, b_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_A_a_b_Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){A_Ux_judgement, a_A_judgement, b_A_judgement}, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id is_trunc = p_define_is_trunc(e);
    tt_id is_trunc_Ux__pi_Ux_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){is_trunc, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id is_trunc_eq_A_a_b_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            is_trunc_Ux__pi_Ux_Ux_judgement,
            eq_A_a_b_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_b_A_is_trunc_eq_A_a_b_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, is_trunc_eq_A_a_b_Ux_judgement}, 2, 0, (tt_id[]){b_A_context}, 1, __FILE__, __LINE__);
    tt_id pi_a_A_pi_b_A_is_trunc_eq_A_a_b_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            A_Ux_judgement,
            pi_b_A_is_trunc_eq_A_a_b_Ux_judgement,
        }, 2, 0, (tt_id[]){a_A_context}, 1, __FILE__, __LINE__);
    tt_id pi_A_pi_a_A_pi_b_A_is_trunc_eq_A_a_b_Ux_Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
                Ux_UUOmega_judgement,
                pi_a_A_pi_b_A_is_trunc_eq_A_a_b_Ux_judgement,
            }, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id pi_Ux_pi_A_pi_a_A_pi_b_A_is_trunc_eq_A_a_b_Ux_Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
                UUOmega_UUKappa_judgement,
                pi_A_pi_a_A_pi_b_A_is_trunc_eq_A_a_b_Ux_Ux_judgement,
            }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id defeq_is_set = proof_step(e, TT_Def, (tt_id[]){pi_Ux_pi_A_pi_a_A_pi_b_A_is_trunc_eq_A_a_b_Ux_Ux_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_is_set}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

tt_id p_define_is_trunc(tt_engine *e) {
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id x_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id y_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id x_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, x_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id y_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, y_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_A_x_y__Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){A_Ux_judgement, x_A_judgement, y_A_judgement}, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_yA_eq_A_x_y__Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, eq_A_x_y__Ux_judgement}, 2, 0, (tt_id[]){y_A_context}, 1, __FILE__, __LINE__);
    tt_id pi_xA_pi_yA_eq_A_x_y__Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, pi_yA_eq_A_x_y__Ux_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id A_pi_xA_pi_yA_eq_A_x_y__Ux_Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            Ux_UUOmega_judgement,
            pi_xA_pi_yA_eq_A_x_y__Ux_judgement,
        }, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id is_trunc_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            UUOmega_UUKappa_judgement,
            A_pi_xA_pi_yA_eq_A_x_y__Ux_Ux_judgement,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id defeq_is_trunc = proof_step(e, TT_Def, (tt_id[]){is_trunc_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_is_trunc}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

tt_id p_define_lem(tt_engine *e) {
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id void_judgement = p_define_void(e);
    tt_id pi_A_void_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, void_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id pi_pi_A_void_void__Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){pi_A_void_judgement, void_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    proof_tuple tuple_1 = p_define_propositional_truncation(e);
    tt_id trunc_form_axiom = tuple_1.v[0];
    tt_id trunc_Ux_pi_Ux_U0 = proof_step(e, TT_PiElim, (tt_id[]){trunc_form_axiom, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id trunc_Ux_A_U0_judgement = proof_step(e, TT_PiElim, (tt_id[]){trunc_Ux_pi_Ux_U0, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_pi_A_void_void_trunc_Ux_A_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            pi_pi_A_void_void__Ux_judgement,
            trunc_Ux_A_U0_judgement,
        }, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id pi_A_pi_pi_A_void_void_trunc_Ux_A_UUOmega_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                Ux_UUOmega_judgement,
                pi_pi_A_void_void_trunc_Ux_A_judgement,
            }, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id pi_Ux_pi_A_pi_pi_A_void_void_trunc_Ux_A_UUOmega_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                UUOmega_UUKappa_judgement,
                pi_A_pi_pi_A_void_void_trunc_Ux_A_UUOmega_judgement,
            }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    return proof_step(e, TT_Axiom, (tt_id[]){pi_Ux_pi_A_pi_pi_A_void_void_trunc_Ux_A_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

proof_tuple p_define_nat(tt_engine *e) {
    tt_id Nat_U0_judgement = proof_step(e, TT_NatForm, (tt_id[]){0}, 0, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id zero_Nat_judgement = proof_step(e, TT_NatIntroZ, (tt_id[]){0}, 0, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return (proof_tuple){{Nat_U0_judgement, zero_Nat_judgement}};
}

tt_id p_define_not(tt_engine *e) {
    tt_id Void_U0_judgement = p_define_void(e);
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_A_Void_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, Void_U0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id lam_A_pi_A_Void__pi_Ux_Ux = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, pi_A_Void_Ux_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id not_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            UUOmega_UUKappa_judgement,
            lam_A_pi_A_Void__pi_Ux_Ux,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id defeq_not = proof_step(e, TT_Def, (tt_id[]){not_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_not}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

tt_id p_define_pi_void_unique(tt_engine *e) {
    tt_id Void_U0_judgement = p_define_void(e);
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    proof_tuple tuple_1 = p_define_homotopy(e);
    tt_id def_homotopy = tuple_1.v[0];
    tt_id _def_happly = tuple_1.v[1];
    tt_id _def_ap = tuple_1.v[2];
    tt_id _def_id = tuple_1.v[3];
    tt_id _def_isequiv = tuple_1.v[4];
    tt_id funext_axiom = tuple_1.v[5];
    tt_id _funext_compute_axiom = tuple_1.v[6];
    tt_id _funext_unique_axiom = tuple_1.v[7];
    tt_id _def_id_isequiv = tuple_1.v[8];
    tt_id _def_ueqequiv = tuple_1.v[9];
    tt_id _univalence_axiom = tuple_1.v[10];
    tt_id _def_transport = tuple_1.v[11];
    tt_id _ua_elim_axiom = tuple_1.v[12];
    tt_id _ua_unique_axiom = tuple_1.v[13];
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_Void_A_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){Void_U0_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id f_pi_Void_A_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_Void_A_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id f_pi_Void_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, f_pi_Void_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id g_pi_Void_A_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_Void_A_Ux_judgement}, 1, 0, (tt_id[]){f_pi_Void_A_context}, 1, __FILE__, __LINE__);
    tt_id g_pi_Void_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, g_pi_Void_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id x_Void_context = proof_step(e, TT_CtxExt, (tt_id[]){Void_U0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id x_Void_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, x_Void_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_x_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){f_pi_Void_A_judgement, x_Void_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id g_x_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){g_pi_Void_A_judgement, x_Void_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_x_eq_g_x_Ux_judgement = proof_step(e, TT_EqForm, (tt_id[]){
            A_Ux_judgement,
            f_x_A_judgement,
            g_x_A_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id indvoid_x_f_x_eq_g_x_judgement = proof_step(e, TT_VoidElim, (tt_id[]){f_x_eq_g_x_Ux_judgement, x_Void_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id lam_x_IndVoid_x__pi_x_Void_eq_A_f_x_g_x_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Void_U0_judgement, indvoid_x_f_x_eq_g_x_judgement}, 2, 0, (tt_id[]){x_Void_context}, 1, __FILE__, __LINE__);
    tt_id homotopy_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_homotopy, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Void_Ux_judgement = proof_step(e, TT_UCumul0, (tt_id[]){Void_U0_judgement, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_Void_judgement = proof_step(e, TT_PiElim, (tt_id[]){homotopy_Ux_judgement, Void_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_i_A__pi_Void_Ux_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Void_U0_judgement, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id homotopy_Ux_Void_lam_i_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            homotopy_Ux_Void_judgement,
            lam_i_A__pi_Void_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    homotopy_Ux_Void_lam_i_A_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){homotopy_Ux_Void_lam_i_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_Void_lam_i_A_f_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            homotopy_Ux_Void_lam_i_A_judgement,
            f_pi_Void_A_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_Ux_Void_lam_i_A_f_g_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            homotopy_Ux_Void_lam_i_A_f_judgement,
            g_pi_Void_A_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lookup_homotopy_def = proof_step(e, TT_HighExp, (tt_id[]){def_homotopy}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    lookup_homotopy_def = proof_step(e, TT_DefLookup, (tt_id[]){lookup_homotopy_def}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id homotopy_reduce = proof_step(e, TT_DefEqRefl, (tt_id[]){homotopy_Ux_Void_lam_i_A_f_g_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    homotopy_reduce = proof_step(e, TT_HighExp, (tt_id[]){homotopy_reduce}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    homotopy_reduce = proof_step(e, TT_High0, (tt_id[]){homotopy_reduce}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    homotopy_reduce = proof_step(e, TT_HighSubs, (tt_id[]){homotopy_reduce, lookup_homotopy_def}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned _i=0; _i<2; ++_i) {
    homotopy_reduce = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){homotopy_reduce}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id homotopy_f_g_judgement = proof_step(e, TT_Subs, (tt_id[]){
            lam_x_IndVoid_x__pi_x_Void_eq_A_f_x_g_x_judgement,
            homotopy_reduce,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){funext_axiom, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_Void_judgement = proof_step(e, TT_PiElim, (tt_id[]){funext_Ux_judgement, Void_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_Void_lam_i_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            funext_Ux_Void_judgement,
            lam_i_A__pi_Void_Ux_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    funext_Ux_Void_lam_i_A_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){funext_Ux_Void_lam_i_A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_Void_lam_i_A_f_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            funext_Ux_Void_lam_i_A_judgement,
            f_pi_Void_A_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_Void_lam_i_A_f_g_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            funext_Ux_Void_lam_i_A_f_judgement,
            g_pi_Void_A_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id funext_Ux_Void_lam_i_A_f_g_lam_x_IndVoid_x_judgement = proof_step(e, TT_PiElim, (tt_id[]){
                funext_Ux_Void_lam_i_A_f_g_judgement,
                homotopy_f_g_judgement,
            }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_f_piVoidUniq_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_Void_A_Ux_judgement,
            funext_Ux_Void_lam_i_A_f_g_lam_x_IndVoid_x_judgement,
        }, 2, 0, (tt_id[]){g_pi_Void_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_piVoidUniq_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_Void_A_Ux_judgement,
            Ux_A_f_piVoidUniq_judgement,
        }, 2, 0, (tt_id[]){f_pi_Void_A_context}, 1, __FILE__, __LINE__);
    tt_id Ux_piVoidUniq_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_piVoidUniq_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id piVoidUniq_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_piVoidUniq_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id defeq_piVoidUniq = proof_step(e, TT_Def, (tt_id[]){piVoidUniq_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_piVoidUniq}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

proof_tuple p_define_pr(tt_engine *e) {
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_A_Ux__UUOmega_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id B__pi_A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_A_Ux__UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id B__pi_A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, B__pi_A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id x_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id x_A_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, x_A_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id B_x__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){B__pi_A_Ux_judgement, x_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id sigma_x_A__B_x__Ux_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){A_Ux_judgement, B_x__Ux_judgement}, 2, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id z_sigma_xA_Bx_context = proof_step(e, TT_CtxExt, (tt_id[]){sigma_x_A__B_x__Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id z_sigma_xA_Bx_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, z_sigma_xA_Bx_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id y_Bx_context = proof_step(e, TT_CtxExt, (tt_id[]){B_x__Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id y_Bx_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, y_Bx_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_B_z_pr1_judgement = proof_step(e, TT_SigmaElim, (tt_id[]){
            A_Ux_judgement,
            x_A_judgement,
            z_sigma_xA_Bx_judgement,
        }, 3, 0, (tt_id[]){0, x_A_context, y_Bx_context}, 3, __FILE__, __LINE__);
    tt_id Ux_A_B_pr1_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            sigma_x_A__B_x__Ux_judgement,
            Ux_A_B_z_pr1_judgement,
        }, 2, 0, (tt_id[]){z_sigma_xA_Bx_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_pr1_judgement = proof_step(e, TT_PiIntro, (tt_id[]){pi_A_Ux__UUOmega_judgement, Ux_A_B_pr1_judgement}, 2, 0, (tt_id[]){B__pi_A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id Ux_pr1_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_pr1_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id pr1_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_pr1_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id pr1_defeq_judgement = proof_step(e, TT_Def, (tt_id[]){pr1_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_pr1 = proof_step(e, TT_DefEqExtL, (tt_id[]){pr1_defeq_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id tpl_x_y__sigma_xA_Bx_judgement = proof_step(e, TT_SigmaIntro, (tt_id[]){
            x_A_judgement,
            B_x__Ux_judgement,
            y_Bx_judgement,
        }, 3, 0, (tt_id[]){x_A_context}, 1, __FILE__, __LINE__);
    tt_id pr1_tpl_x_y__A_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            Ux_A_B_pr1_judgement,
            tpl_x_y__sigma_xA_Bx_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr1_z_A_judgement = proof_step(e, TT_PiElim, (tt_id[]){Ux_A_B_pr1_judgement, z_sigma_xA_Bx_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id B_pr1_x_y__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){B__pi_A_Ux_judgement, pr1_z_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id defeq_B_pr1_tpl_x_y__Ux_judgement = proof_step(e, TT_DefEqRefl, (tt_id[]){pr1_tpl_x_y__A_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    defeq_B_pr1_tpl_x_y__Ux_judgement = proof_step(e, TT_HighExp, (tt_id[]){defeq_B_pr1_tpl_x_y__Ux_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    defeq_B_pr1_tpl_x_y__Ux_judgement = proof_step(e, TT_High0, (tt_id[]){defeq_B_pr1_tpl_x_y__Ux_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_1=0; loop_1<2; ++loop_1) {
    defeq_B_pr1_tpl_x_y__Ux_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){defeq_B_pr1_tpl_x_y__Ux_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id y_B_indsigma_rsr_tpl_x_y = proof_step(e, TT_Subs, (tt_id[]){y_Bx_judgement, defeq_B_pr1_tpl_x_y__Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_B_x_y_pr2_judgement = proof_step(e, TT_SigmaElim, (tt_id[]){
            B_pr1_x_y__Ux_judgement,
            y_B_indsigma_rsr_tpl_x_y,
            tpl_x_y__sigma_xA_Bx_judgement,
        }, 3, 0, (tt_id[]){
            z_sigma_xA_Bx_context,
            x_A_context,
            y_Bx_context,
        }, 3, __FILE__, __LINE__);
    tt_id B_pr1_z__Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){B__pi_A_Ux_judgement, pr1_z_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_A_B_z_pr2_judgement = proof_step(e, TT_SigmaElim, (tt_id[]){
            B_pr1_z__Ux_judgement,
            Ux_A_B_x_y_pr2_judgement,
            z_sigma_xA_Bx_judgement,
        }, 3, 0, (tt_id[]){
            z_sigma_xA_Bx_context,
            x_A_context,
            y_Bx_context,
        }, 3, __FILE__, __LINE__);
    tt_id Ux_A_B_pr2_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            sigma_x_A__B_x__Ux_judgement,
            Ux_A_B_z_pr2_judgement,
        }, 2, 0, (tt_id[]){z_sigma_xA_Bx_context}, 1, __FILE__, __LINE__);
    tt_id Ux_A_pr2_judgement = proof_step(e, TT_PiIntro, (tt_id[]){pi_A_Ux__UUOmega_judgement, Ux_A_B_pr2_judgement}, 2, 0, (tt_id[]){B__pi_A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id Ux_pr2_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Ux_UUOmega_judgement, Ux_A_pr2_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id pr2_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_pr2_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    for (unsigned loop_2=0; loop_2<2; ++loop_2) {
    pr2_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){pr2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id pr2_defeq_judgement = proof_step(e, TT_Def, (tt_id[]){pr2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_pr2 = proof_step(e, TT_DefEqExtL, (tt_id[]){pr2_defeq_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return (proof_tuple){{def_pr1, def_pr2}};
}

proof_tuple p_define_propositional_truncation(tt_engine *e) {
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id U0_judgement = p_define_u0(e);
    tt_id pi_Ux_U0_UUOmega_judgement = proof_step(e, TT_PiForm, (tt_id[]){Ux_UUOmega_judgement, U0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id pi_Ux_UUOmega_pi_Ux_U0__UUKappa_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            UUOmega_UUKappa_judgement,
            pi_Ux_U0_UUOmega_judgement,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id trunc_form_axiom = proof_step(e, TT_Axiom, (tt_id[]){pi_Ux_UUOmega_pi_Ux_U0__UUKappa_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id trunc_Ux = proof_step(e, TT_PiElim, (tt_id[]){trunc_form_axiom, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, A_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id trunc_Ux_A_U0_judgement = proof_step(e, TT_PiElim, (tt_id[]){trunc_Ux, A_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id U0_UUOmega_judgement = proof_step(e, TT_UCumulOmega, (tt_id[]){U0_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id is_trunc = p_define_is_trunc(e);
    tt_id is_trunc_U0__pi_U0_U0_judgement = proof_step(e, TT_PiElim, (tt_id[]){is_trunc, U0_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id is_trunc_trunc_Ux_A_U0_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            is_trunc_U0__pi_U0_U0_judgement,
            trunc_Ux_A_U0_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_AUx_is_trunc_trunc_Ux_A_U0__Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            Ux_UUOmega_judgement,
            is_trunc_trunc_Ux_A_U0_judgement,
        }, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id pi_Ux_UUOmega_pi_AUx_is_trunc_trunc_Ux_A_U0__UUKappa_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                UUOmega_UUKappa_judgement,
                pi_AUx_is_trunc_trunc_Ux_A_U0__Ux_judgement,
            }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id trunc_is_trunc_axiom = proof_step(e, TT_Axiom, (tt_id[]){pi_Ux_UUOmega_pi_AUx_is_trunc_trunc_Ux_A_U0__UUKappa_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id B_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){Ux_UUOmega_judgement}, 1, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id B_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, B_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_arrow_B_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){Ux_UUOmega_judgement, B_Ux_judgement}, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id is_trunc_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){is_trunc, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id is_trunc_Ux_B_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){is_trunc_Ux_judgement, B_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_arrow_B_X_is_trunc_Ux_B_Ux_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){A_arrow_B_Ux_judgement, is_trunc_Ux_B_Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id trunc_Ux_A_arrow_B_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){trunc_Ux_A_U0_judgement, B_Ux_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id A_arrow_B_X_is_trunc_Ux_B_Ux_arrow_trunc_Ux_A_arrow_B_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                A_arrow_B_X_is_trunc_Ux_B_Ux_judgement,
                trunc_Ux_A_arrow_B_Ux_judgement,
            }, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id pi_B_Ux_A_arrow_B_X_is_trunc_Ux_B_Ux_arrow_trunc_Ux_A_arrow_B_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                Ux_UUOmega_judgement,
                A_arrow_B_X_is_trunc_Ux_B_Ux_arrow_trunc_Ux_A_arrow_B_Ux_judgement,
            }, 2, 0, (tt_id[]){B_Ux_context}, 1, __FILE__, __LINE__);
    tt_id pi_AUx_pi_B_Ux_A_arrow_B_X_is_trunc_Ux_B_Ux_arrow_trunc_Ux_A_arrow_B_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                Ux_UUOmega_judgement,
                pi_B_Ux_A_arrow_B_X_is_trunc_Ux_B_Ux_arrow_trunc_Ux_A_arrow_B_Ux_judgement,
            }, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id pi_Ux_pi_AUx_pi_B_Ux_A_arrow_B_X_is_trunc_Ux_B_Ux_arrow_trunc_Ux_A_arrow_B_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){
                UUOmega_UUKappa_judgement,
                pi_AUx_pi_B_Ux_A_arrow_B_X_is_trunc_Ux_B_Ux_arrow_trunc_Ux_A_arrow_B_Ux_judgement
                    ,
            }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id truncation_elimination_axiom = proof_step(e, TT_Axiom, (tt_id[]){
            pi_Ux_pi_AUx_pi_B_Ux_A_arrow_B_X_is_trunc_Ux_B_Ux_arrow_trunc_Ux_A_arrow_B_Ux_judgement
                ,
        }, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_arrow_trunc_Ux_A_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_Ux_judgement, trunc_Ux_A_U0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id pi_AUx_A_arrow_trunc_Ux_A_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            Ux_UUOmega_judgement,
            A_arrow_trunc_Ux_A_Ux_judgement,
        }, 2, 0, (tt_id[]){A_Ux_context}, 1, __FILE__, __LINE__);
    tt_id pi_Ux_pi_AUx_A_arrow_trunc_Ux_A_Ux_judgement = proof_step(e, TT_PiForm, (tt_id[]){
            UUOmega_UUKappa_judgement,
            pi_AUx_A_arrow_trunc_Ux_A_Ux_judgement,
        }, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id trunc_intro_axiom = proof_step(e, TT_Axiom, (tt_id[]){pi_Ux_pi_AUx_A_arrow_trunc_Ux_A_Ux_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return (proof_tuple){{trunc_form_axiom, trunc_intro_axiom, trunc_is_trunc_axiom, truncation_elimination_axiom}};
}

tt_id p_define_singleton(tt_engine *e) {
    return proof_step(e, TT_UnitIntro, (tt_id[]){0}, 0, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

proof_tuple p_define_two(tt_engine *e) {
    tt_id Unit_U0_judgement = p_define_unit(e);
    tt_id singleton_Unit_judgement = p_define_singleton(e);
    tt_id UUOmega_UUKappa_judgement = p_define_uuomega(e);
    tt_id p_Unit_Unit_U0_judgement = proof_step(e, TT_SumForm, (tt_id[]){Unit_U0_judgement, Unit_U0_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id two_form_defeq = proof_step(e, TT_Def, (tt_id[]){p_Unit_Unit_U0_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id two_form_defeq_backwards = proof_step(e, TT_DefEqSwp, (tt_id[]){two_form_defeq}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_two = proof_step(e, TT_DefEqExtL, (tt_id[]){two_form_defeq}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id zero__p_unit_unit_judgement = proof_step(e, TT_SumIntroL, (tt_id[]){
            Unit_U0_judgement,
            Unit_U0_judgement,
            singleton_Unit_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id zero_two_judgement = proof_step(e, TT_Subs, (tt_id[]){
            zero__p_unit_unit_judgement,
            two_form_defeq_backwards,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id zero_two_defeq = proof_step(e, TT_Def, (tt_id[]){zero_two_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_zero_two = proof_step(e, TT_DefEqExtL, (tt_id[]){zero_two_defeq}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id one__p_unit_unit_judgement = proof_step(e, TT_SumIntroR, (tt_id[]){
            Unit_U0_judgement,
            Unit_U0_judgement,
            singleton_Unit_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id one_two_judgement = proof_step(e, TT_Subs, (tt_id[]){
            one__p_unit_unit_judgement,
            two_form_defeq_backwards,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id one_two_defeq = proof_step(e, TT_Def, (tt_id[]){one_two_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_one_two = proof_step(e, TT_DefEqExtL, (tt_id[]){one_two_defeq}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id i_two_context = proof_step(e, TT_CtxExt, (tt_id[]){def_two}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id i_Two_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, i_two_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id i_p_Unit_Unit_judgement = proof_step(e, TT_Subs, (tt_id[]){i_Two_judgement, two_form_defeq}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_UUOmega_context = proof_step(e, TT_CtxExt, (tt_id[]){UUOmega_UUKappa_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id Ux_UUOmega_judgement = proof_step(e, TT_UVble, (tt_id[]){0}, 0, Ux_UUOmega_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pi_Two_Ux_UUOmega_judgement = proof_step(e, TT_PiForm, (tt_id[]){def_two, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id C_pi_Two_Ux_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_Two_Ux_UUOmega_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id C_pi_Two_Ux_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, C_pi_Two_Ux_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id C_pi_p_Unit_Unit_Ux_judgement = proof_step(e, TT_Subs, (tt_id[]){C_pi_Two_Ux_judgement, two_form_defeq}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id e0_p_Unit_Unit_context = proof_step(e, TT_CtxExt, (tt_id[]){p_Unit_Unit_U0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id e0_p_Unit_Unit_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, e0_p_Unit_Unit_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id C_e0_p_Unit_Unit_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            C_pi_p_Unit_Unit_Ux_judgement,
            e0_p_Unit_Unit_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id x_Unit_context = proof_step(e, TT_CtxExt, (tt_id[]){Unit_U0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id x_Unit_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, x_Unit_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id inl_x_p_Unit_Unit_judgement = proof_step(e, TT_SumIntroL, (tt_id[]){
            Unit_U0_judgement,
            Unit_U0_judgement,
            x_Unit_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id inr_x_p_Unit_Unit_judgement = proof_step(e, TT_SumIntroR, (tt_id[]){
            Unit_U0_judgement,
            Unit_U0_judgement,
            x_Unit_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id C_inl_x_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            C_pi_p_Unit_Unit_Ux_judgement,
            inl_x_p_Unit_Unit_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id C_inr_x_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            C_pi_p_Unit_Unit_Ux_judgement,
            inr_x_p_Unit_Unit_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id C_Zero2_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){C_pi_Two_Ux_judgement, def_zero_two}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id C_One2_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){C_pi_Two_Ux_judgement, def_one_two}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id c_C_Zero2_context = proof_step(e, TT_CtxExt, (tt_id[]){C_Zero2_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id d_C_One2_context = proof_step(e, TT_CtxExt, (tt_id[]){C_One2_Ux_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id c_C_Zero2_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, c_C_Zero2_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id d_C_One2_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, d_C_One2_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id c_C_inl_singleton_Ux_judgement = proof_step(e, TT_Subs, (tt_id[]){c_C_Zero2_judgement, zero_two_defeq}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id d_C_inr_singleton_Ux_judgement = proof_step(e, TT_Subs, (tt_id[]){d_C_One2_judgement, one_two_defeq}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id c_indunit__C_inl_x_judgement = proof_step(e, TT_UnitElim, (tt_id[]){
            C_inl_x_Ux_judgement,
            c_C_inl_singleton_Ux_judgement,
            x_Unit_judgement,
        }, 3, 0, (tt_id[]){x_Unit_context}, 1, __FILE__, __LINE__);
    tt_id d_indunit__C_inr_x_judgement = proof_step(e, TT_UnitElim, (tt_id[]){
            C_inr_x_Ux_judgement,
            d_C_inr_singleton_Ux_judgement,
            x_Unit_judgement,
        }, 3, 0, (tt_id[]){x_Unit_context}, 1, __FILE__, __LINE__);
    tt_id Ux_C_c_d_e0_indsum_judgement = proof_step(e, TT_SumElim, (tt_id[]){
            C_e0_p_Unit_Unit_Ux_judgement,
            c_indunit__C_inl_x_judgement,
            d_indunit__C_inr_x_judgement,
            e0_p_Unit_Unit_judgement,
        }, 4, 0, (tt_id[]){
            e0_p_Unit_Unit_context,
            x_Unit_context,
            x_Unit_context,
        }, 3, __FILE__, __LINE__);
    tt_id Ux_C_c_d_lambda_e0_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            p_Unit_Unit_U0_judgement,
            Ux_C_c_d_e0_indsum_judgement,
        }, 2, 0, (tt_id[]){e0_p_Unit_Unit_context}, 1, __FILE__, __LINE__);
    tt_id Ux_C_c_d_i_indsum_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            Ux_C_c_d_lambda_e0_judgement,
            i_p_Unit_Unit_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_C_c_d_i_ind2_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){Ux_C_c_d_i_indsum_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_C_c_d_ind2_judgement = proof_step(e, TT_PiIntro, (tt_id[]){def_two, Ux_C_c_d_i_ind2_judgement}, 2, 0, (tt_id[]){i_two_context}, 1, __FILE__, __LINE__);
    tt_id Ux_C_c_ind2_judgement = proof_step(e, TT_PiIntro, (tt_id[]){C_One2_Ux_judgement, Ux_C_c_d_ind2_judgement}, 2, 0, (tt_id[]){d_C_One2_context}, 1, __FILE__, __LINE__);
    tt_id Ux_C_ind2_judgement = proof_step(e, TT_PiIntro, (tt_id[]){C_Zero2_Ux_judgement, Ux_C_c_ind2_judgement}, 2, 0, (tt_id[]){c_C_Zero2_context}, 1, __FILE__, __LINE__);
    tt_id Ux_ind2_judgement = proof_step(e, TT_PiIntro, (tt_id[]){pi_Two_Ux_UUOmega_judgement, Ux_C_ind2_judgement}, 2, 0, (tt_id[]){C_pi_Two_Ux_context}, 1, __FILE__, __LINE__);
    tt_id ind2_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_ind2_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id defeq_ind2 = proof_step(e, TT_Def, (tt_id[]){ind2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_ind2 = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_ind2}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_ind2_Ux_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_ind2, Ux_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_C_ind2_Ux_C_judgement = proof_step(e, TT_PiElim, (tt_id[]){Ux_ind2_Ux_judgement, C_pi_Two_Ux_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_C_c_ind2_Ux_C_c_judgement = proof_step(e, TT_PiElim, (tt_id[]){Ux_C_ind2_Ux_C_judgement, c_C_Zero2_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_C_c_d_ind2_Ux_C_c_d_judgement = proof_step(e, TT_PiElim, (tt_id[]){Ux_C_c_ind2_Ux_C_c_judgement, d_C_One2_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_C_c_d_ind2_Ux_C_c_d_Zero2_judgement = proof_step(e, TT_PiElim, (tt_id[]){Ux_C_c_d_ind2_Ux_C_c_d_judgement, def_zero_two}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_C_c_d_comp2_0_judgement = proof_step(e, TT_DefEqRefl, (tt_id[]){Ux_C_c_d_ind2_Ux_C_c_d_Zero2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    Ux_C_c_d_comp2_0_judgement = proof_step(e, TT_HighExp, (tt_id[]){Ux_C_c_d_comp2_0_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    Ux_C_c_d_comp2_0_judgement = proof_step(e, TT_High1, (tt_id[]){Ux_C_c_d_comp2_0_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    Ux_C_c_d_comp2_0_judgement = proof_step(e, TT_HighSubs, (tt_id[]){Ux_C_c_d_comp2_0_judgement, defeq_ind2}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    Ux_C_c_d_comp2_0_judgement = proof_step(e, TT_HighSubs, (tt_id[]){Ux_C_c_d_comp2_0_judgement, zero_two_defeq}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_1=0; loop_1<3; ++loop_1) {
    Ux_C_c_d_comp2_0_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){Ux_C_c_d_comp2_0_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id Ux_C_c_comp2_0_judgement = proof_step(e, TT_PiIntro, (tt_id[]){C_One2_Ux_judgement, Ux_C_c_d_comp2_0_judgement}, 2, 0, (tt_id[]){d_C_One2_context}, 1, __FILE__, __LINE__);
    tt_id Ux_C_comp2_0_judgement = proof_step(e, TT_PiIntro, (tt_id[]){C_Zero2_Ux_judgement, Ux_C_c_comp2_0_judgement}, 2, 0, (tt_id[]){c_C_Zero2_context}, 1, __FILE__, __LINE__);
    tt_id Ux_comp2_0_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_Two_Ux_UUOmega_judgement,
            Ux_C_comp2_0_judgement,
        }, 2, 0, (tt_id[]){C_pi_Two_Ux_context}, 1, __FILE__, __LINE__);
    tt_id comp2_0_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_comp2_0_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    tt_id Ux_C_c_d_ind2_Ux_C_c_d_One2_judgement = proof_step(e, TT_PiElim, (tt_id[]){Ux_C_c_d_ind2_Ux_C_c_d_judgement, def_one_two}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Ux_C_c_d_comp2_1_judgement = proof_step(e, TT_DefEqRefl, (tt_id[]){Ux_C_c_d_ind2_Ux_C_c_d_One2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    Ux_C_c_d_comp2_1_judgement = proof_step(e, TT_HighExp, (tt_id[]){Ux_C_c_d_comp2_1_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    Ux_C_c_d_comp2_1_judgement = proof_step(e, TT_High1, (tt_id[]){Ux_C_c_d_comp2_1_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    Ux_C_c_d_comp2_1_judgement = proof_step(e, TT_HighSubs, (tt_id[]){Ux_C_c_d_comp2_1_judgement, defeq_ind2}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    Ux_C_c_d_comp2_1_judgement = proof_step(e, TT_HighSubs, (tt_id[]){Ux_C_c_d_comp2_1_judgement, one_two_defeq}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    for (unsigned loop_2=0; loop_2<3; ++loop_2) {
    Ux_C_c_d_comp2_1_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){Ux_C_c_d_comp2_1_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}
    tt_id Ux_C_c_comp2_1_judgement = proof_step(e, TT_PiIntro, (tt_id[]){C_One2_Ux_judgement, Ux_C_c_d_comp2_1_judgement}, 2, 0, (tt_id[]){d_C_One2_context}, 1, __FILE__, __LINE__);
    tt_id Ux_C_comp2_1_judgement = proof_step(e, TT_PiIntro, (tt_id[]){C_Zero2_Ux_judgement, Ux_C_c_comp2_1_judgement}, 2, 0, (tt_id[]){c_C_Zero2_context}, 1, __FILE__, __LINE__);
    tt_id Ux_comp2_1_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_Two_Ux_UUOmega_judgement,
            Ux_C_comp2_1_judgement,
        }, 2, 0, (tt_id[]){C_pi_Two_Ux_context}, 1, __FILE__, __LINE__);
    tt_id comp2_1_judgement = proof_step(e, TT_PiIntro, (tt_id[]){UUOmega_UUKappa_judgement, Ux_comp2_1_judgement}, 2, 0, (tt_id[]){Ux_UUOmega_context}, 1, __FILE__, __LINE__);
    return (proof_tuple){{def_two, def_zero_two, def_one_two, def_ind2, comp2_0_judgement, comp2_1_judgement}};
}

tt_id p_define_u0(tt_engine *e) {
    return proof_step(e, TT_UIntro0, (tt_id[]){0}, 0, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

tt_id p_define_unit(tt_engine *e) {
    return proof_step(e, TT_UnitForm, (tt_id[]){0}, 0, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

tt_id p_define_unit_prop_unique(tt_engine *e) {
    tt_id Unit_U0_judgement = p_define_unit(e);
    tt_id singleton_Unit_judgement = p_define_singleton(e);
    tt_id a_Unit_context = proof_step(e, TT_CtxExt, (tt_id[]){Unit_U0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id a_Unit_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, a_Unit_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id eq_Unit_a_singleton_judgement = proof_step(e, TT_EqForm, (tt_id[]){
            Unit_U0_judgement,
            a_Unit_judgement,
            singleton_Unit_judgement,
        }, 3, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id Refl_singleton__eq_Unit_singleton_singleton_judgement = proof_step(e, TT_EqIntro, (tt_id[]){singleton_Unit_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id IndUnit__eq_Unit_a_singleton_judgement = proof_step(e, TT_UnitElim, (tt_id[]){
            eq_Unit_a_singleton_judgement,
            Refl_singleton__eq_Unit_singleton_singleton_judgement,
            a_Unit_judgement,
        }, 3, 0, (tt_id[]){a_Unit_context}, 1, __FILE__, __LINE__);
    tt_id lam_a_IndUnit__pi_a_Unit_eq_Unit_a_singleton_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
                Unit_U0_judgement,
                IndUnit__eq_Unit_a_singleton_judgement,
            }, 2, 0, (tt_id[]){a_Unit_context}, 1, __FILE__, __LINE__);
    tt_id defeq_UnitUniq = proof_step(e, TT_Def, (tt_id[]){lam_a_IndUnit__pi_a_Unit_eq_Unit_a_singleton_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_UnitUniq}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

tt_id p_define_uuomega(tt_engine *e) {
    return proof_step(e, TT_UIntroOmega, (tt_id[]){0}, 0, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

tt_id p_define_void(tt_engine *e) {
    return proof_step(e, TT_VoidForm, (tt_id[]){0}, 0, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
}

proof_tuple p_define_wnat(tt_engine *e) {
    proof_tuple tuple_1 = p_define_two(e);
    tt_id def_two = tuple_1.v[0];
    tt_id def_zero_two = tuple_1.v[1];
    tt_id def_one_two = tuple_1.v[2];
    tt_id def_ind2 = tuple_1.v[3];
    tt_id comp2_0_judgement = tuple_1.v[4];
    tt_id comp2_1_judgement = tuple_1.v[5];
    proof_tuple tuple_2 = p_define_homotopy(e);
    tt_id _def_homotopy = tuple_2.v[0];
    tt_id _def_happly = tuple_2.v[1];
    tt_id _def_ap = tuple_2.v[2];
    tt_id _def_id = tuple_2.v[3];
    tt_id _def_isequiv = tuple_2.v[4];
    tt_id _funext_axiom = tuple_2.v[5];
    tt_id _funext_compute_axiom = tuple_2.v[6];
    tt_id _funext_unique_axiom = tuple_2.v[7];
    tt_id _def_id_isequiv = tuple_2.v[8];
    tt_id _def_ueqequiv = tuple_2.v[9];
    tt_id _univalence_axiom = tuple_2.v[10];
    tt_id _def_transport = tuple_2.v[11];
    tt_id _ua_elim_axiom = tuple_2.v[12];
    tt_id _ua_unique_axiom = tuple_2.v[13];
    tt_id Void_U0_judgement = p_define_void(e);
    tt_id Unit_U0_judgement = p_define_unit(e);
    tt_id singleton_Unit_judgement = p_define_singleton(e);
    tt_id U0_U1_judgement = p_define_u0(e);
    tt_id U1_U2_judgement = proof_step(e, TT_UIntro, (tt_id[]){U0_U1_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id U1_UUOmega_judgement = proof_step(e, TT_UCumulOmega, (tt_id[]){U1_U2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id type_for_arity_judgement = proof_step(e, TT_PiIntro, (tt_id[]){def_two, U0_U1_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id ind2_U1_judgement = proof_step(e, TT_PiElim, (tt_id[]){def_ind2, U1_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ind2_U1_lam_i_U0_judgement = proof_step(e, TT_PiElim, (tt_id[]){ind2_U1_judgement, type_for_arity_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ind2_U1_lam_i_U0_reduced_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){ind2_U1_lam_i_U0_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ind2_U1_lam_i_U0_Void_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            ind2_U1_lam_i_U0_reduced_judgement,
            Void_U0_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id arity_type_judgement = proof_step(e, TT_PiElim, (tt_id[]){ind2_U1_lam_i_U0_Void_judgement, Unit_U0_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id i_Two_context = proof_step(e, TT_CtxExt, (tt_id[]){def_two}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id i_Two_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, i_Two_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id arity_i_U0_judgement = proof_step(e, TT_PiElim, (tt_id[]){arity_type_judgement, i_Two_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id WUNat_form_judgement = proof_step(e, TT_WForm, (tt_id[]){def_two, arity_i_U0_judgement}, 2, 0, (tt_id[]){i_Two_context}, 1, __FILE__, __LINE__);
    tt_id defeq_UNat = proof_step(e, TT_Def, (tt_id[]){WUNat_form_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_UNat = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_UNat}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id x_Void_context = proof_step(e, TT_CtxExt, (tt_id[]){Void_U0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id x_Void_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, x_Void_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id comp2_zero_U1_judgement = proof_step(e, TT_PiElim, (tt_id[]){comp2_0_judgement, U1_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id comp2_zero_U1_lam_U0_judgement = proof_step(e, TT_PiElim, (tt_id[]){comp2_zero_U1_judgement, type_for_arity_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id comp2_zero_U1_lam_U0_reduced_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){comp2_zero_U1_lam_U0_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id comp2_zero_U1_lam_U0_Void_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            comp2_zero_U1_lam_U0_reduced_judgement,
            Void_U0_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id comp2_zero_U1_lam_U0_Void_Unit_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            comp2_zero_U1_lam_U0_Void_judgement,
            Unit_U0_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id comp2_zero_arity_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){comp2_zero_U1_lam_U0_Void_Unit_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id comp2_zero_arity_swp_judgement = proof_step(e, TT_DefEqSwp, (tt_id[]){comp2_zero_arity_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id ind_void_Nat_judgement = proof_step(e, TT_VoidElim, (tt_id[]){def_UNat, x_Void_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id zero_pi_Void_UNat_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Void_U0_judgement, ind_void_Nat_judgement}, 2, 0, (tt_id[]){x_Void_context}, 1, __FILE__, __LINE__);
    tt_id arity_function_for_zero_ctor_judgement = proof_step(e, TT_Subs, (tt_id[]){
            zero_pi_Void_UNat_judgement,
            comp2_zero_arity_swp_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    arity_function_for_zero_ctor_judgement = proof_step(e, TT_Subs, (tt_id[]){arity_function_for_zero_ctor_judgement, defeq_UNat}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id defeq_UNat_swp = proof_step(e, TT_DefEqSwp, (tt_id[]){defeq_UNat}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id zero_WUNat_judgement = proof_step(e, TT_WIntro, (tt_id[]){
            def_zero_two,
            arity_i_U0_judgement,
            arity_function_for_zero_ctor_judgement,
        }, 3, 0, (tt_id[]){i_Two_context}, 1, __FILE__, __LINE__);
    tt_id zero_UNat_judgement = proof_step(e, TT_Subs, (tt_id[]){zero_WUNat_judgement, defeq_UNat_swp}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id defeq_zero_UNat = proof_step(e, TT_Def, (tt_id[]){zero_UNat_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_zero_UNat = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_zero_UNat}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id n_UNat_context = proof_step(e, TT_CtxExt, (tt_id[]){def_UNat}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id n_UNat_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, n_UNat_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id _x_Unit_context = proof_step(e, TT_CtxExt, (tt_id[]){Unit_U0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id comp2_one_U1_judgement = proof_step(e, TT_PiElim, (tt_id[]){comp2_1_judgement, U1_UUOmega_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id comp2_one_U1_lam_U0_judgement = proof_step(e, TT_PiElim, (tt_id[]){comp2_one_U1_judgement, type_for_arity_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    comp2_one_U1_lam_U0_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){comp2_one_U1_lam_U0_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id comp2_one_U1_lam_U0_void_judgement = proof_step(e, TT_PiElim, (tt_id[]){comp2_one_U1_lam_U0_judgement, Void_U0_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id comp2_one_U1_lam_U0_void_unit_judgement = proof_step(e, TT_PiElim, (tt_id[]){
            comp2_one_U1_lam_U0_void_judgement,
            Unit_U0_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id comp2_Unit_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){comp2_one_U1_lam_U0_void_unit_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id defeq_Unit_comp2_judgement = proof_step(e, TT_DefEqSwp, (tt_id[]){comp2_Unit_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id unit_to_n_function_judgement = proof_step(e, TT_UnitElim, (tt_id[]){
            def_UNat,
            n_UNat_judgement,
            singleton_Unit_judgement,
        }, 3, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id unit_to_n_function_lam_Unit_judgement = proof_step(e, TT_PiIntro, (tt_id[]){Unit_U0_judgement, unit_to_n_function_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    unit_to_n_function_lam_Unit_judgement = proof_step(e, TT_Subs, (tt_id[]){unit_to_n_function_lam_Unit_judgement, defeq_UNat}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    unit_to_n_function_lam_Unit_judgement = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){unit_to_n_function_lam_Unit_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    unit_to_n_function_lam_Unit_judgement = proof_step(e, TT_HighType, (tt_id[]){unit_to_n_function_lam_Unit_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    unit_to_n_function_lam_Unit_judgement = proof_step(e, TT_HighType, (tt_id[]){unit_to_n_function_lam_Unit_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    unit_to_n_function_lam_Unit_judgement = proof_step(e, TT_High0, (tt_id[]){unit_to_n_function_lam_Unit_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    unit_to_n_function_lam_Unit_judgement = proof_step(e, TT_HighSubs, (tt_id[]){
            unit_to_n_function_lam_Unit_judgement,
            defeq_Unit_comp2_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id n_succ_WUNat_judgement = proof_step(e, TT_WIntro, (tt_id[]){
            def_one_two,
            arity_i_U0_judgement,
            unit_to_n_function_lam_Unit_judgement,
        }, 3, 0, (tt_id[]){i_Two_context}, 1, __FILE__, __LINE__);
    tt_id n_succ_UNat_judgement = proof_step(e, TT_Subs, (tt_id[]){n_succ_WUNat_judgement, defeq_UNat_swp}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id succ_Pi_UNat_UNat_judgement = proof_step(e, TT_PiIntro, (tt_id[]){def_UNat, n_succ_UNat_judgement}, 2, 0, (tt_id[]){n_UNat_context}, 1, __FILE__, __LINE__);
    tt_id defeq_succ = proof_step(e, TT_Def, (tt_id[]){succ_Pi_UNat_UNat_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id def_succ = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_succ}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return (proof_tuple){{def_UNat, def_zero_UNat, def_succ}};
}

proof_tuple p_create_pr1_pr2(tt_engine *e, tt_id U0_judgement) {
    proof_tuple type_var_contexts = proof_type_contexts(e, U0_judgement, 2);
    tt_id A_U0_context = type_var_contexts.v[0];
    tt_id C_U0_context = type_var_contexts.v[1];
    proof_tuple type_vars = proof_variables(e, type_var_contexts);
    tt_id A_U0_judgement = type_vars.v[0];
    tt_id C_U0_judgement = type_vars.v[1];
    tt_id pi_A_U0_U1_judgement = proof_step(e, TT_PiForm, (tt_id[]){A_U0_judgement, U0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id B_pi_A_U0_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_A_U0_U1_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id B_pi_A_U0_judgement = proof_variable(e, B_pi_A_U0_context);
    tt_id a_A_context = proof_step(e, TT_CtxExt, (tt_id[]){A_U0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id a_A_judgement = proof_variable(e, a_A_context);
    tt_id Ba_U0_judgement = proof_step(e, TT_PiElim, (tt_id[]){B_pi_A_U0_judgement, a_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id sigma_xABx_U0_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){A_U0_judgement, Ba_U0_judgement}, 2, 0, (tt_id[]){a_A_context}, 1, __FILE__, __LINE__);
    tt_id b_Ba_context = proof_step(e, TT_CtxExt, (tt_id[]){Ba_U0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id b_Ba_judgement = proof_variable(e, b_Ba_context);
    tt_id p_sigma_xABx_context = proof_step(e, TT_CtxExt, (tt_id[]){sigma_xABx_U0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id p_sigma_xABx_judgement = proof_variable(e, p_sigma_xABx_context);
    tt_id pr1_A_judgement = proof_step(e, TT_SigmaElim, (tt_id[]){
            A_U0_judgement,
            a_A_judgement,
            p_sigma_xABx_judgement,
        }, 3, 0, (tt_id[]){0, a_A_context, b_Ba_context}, 3, __FILE__, __LINE__);
    tt_id pr1_lam_z_sigma_xABx_judgement = proof_step(e, TT_PiIntro, (tt_id[]){sigma_xABx_U0_judgement, pr1_A_judgement}, 2, 0, (tt_id[]){p_sigma_xABx_context}, 1, __FILE__, __LINE__);
    tt_id pr1_lam_B_lam_z_pi_A_sigma_xABx_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_A_U0_U1_judgement,
            pr1_lam_z_sigma_xABx_judgement,
        }, 2, 0, (tt_id[]){B_pi_A_U0_context}, 1, __FILE__, __LINE__);
    tt_id pr1_lam_A_lam_B_lam_z_pi_U0_pi_A_sigma_xABx_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
                U0_judgement,
                pr1_lam_B_lam_z_pi_A_sigma_xABx_judgement,
            }, 2, 0, (tt_id[]){A_U0_context}, 1, __FILE__, __LINE__);
    tt_id a_b__sigma_xABx = proof_step(e, TT_SigmaIntro, (tt_id[]){
            a_A_judgement,
            Ba_U0_judgement,
            b_Ba_judgement,
        }, 3, 0, (tt_id[]){a_A_context}, 1, __FILE__, __LINE__);
    tt_id _pr1_a_b_defeq__A = proof_step(e, TT_PiComp, (tt_id[]){pr1_A_judgement, a_b__sigma_xABx}, 2, 0, (tt_id[]){p_sigma_xABx_context}, 1, __FILE__, __LINE__);
    tt_id pr1_a_b_defeq_a__A = proof_step(e, TT_SigmaComp, (tt_id[]){
            A_U0_judgement,
            a_A_judgement,
            a_A_judgement,
            b_Ba_judgement,
        }, 4, 0, (tt_id[]){0, a_A_context, 0}, 3, __FILE__, __LINE__);
    tt_id a_defeq_pr1_a_b__A = proof_step(e, TT_DefEqSwp, (tt_id[]){pr1_a_b_defeq_a__A}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id b_Bpr1_a_b_judgement = proof_step(e, TT_Subs, (tt_id[]){b_Ba_judgement, a_defeq_pr1_a_b__A}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id B_pr1_p__U_0_judgement = proof_step(e, TT_PiElim, (tt_id[]){B_pi_A_U0_judgement, pr1_A_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr2_Ba_judgement = proof_step(e, TT_SigmaElim, (tt_id[]){
            B_pr1_p__U_0_judgement,
            b_Bpr1_a_b_judgement,
            p_sigma_xABx_judgement,
        }, 3, 0, (tt_id[]){
            p_sigma_xABx_context,
            a_A_context,
            b_Ba_context,
        }, 3, __FILE__, __LINE__);
    tt_id pr2_s1 = proof_step(e, TT_PiIntro, (tt_id[]){sigma_xABx_U0_judgement, pr2_Ba_judgement}, 2, 0, (tt_id[]){p_sigma_xABx_context}, 1, __FILE__, __LINE__);
    tt_id pr2_s2 = proof_step(e, TT_PiIntro, (tt_id[]){pi_A_U0_U1_judgement, pr2_s1}, 2, 0, (tt_id[]){B_pi_A_U0_context}, 1, __FILE__, __LINE__);
    tt_id pr2_judgement = proof_step(e, TT_PiIntro, (tt_id[]){U0_judgement, pr2_s2}, 2, 0, (tt_id[]){A_U0_context}, 1, __FILE__, __LINE__);
    tt_id defeq_pr1 = proof_step(e, TT_Def, (tt_id[]){pr1_lam_A_lam_B_lam_z_pi_U0_pi_A_sigma_xABx_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr1 = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_pr1}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id defeq_pr2 = proof_step(e, TT_Def, (tt_id[]){pr2_judgement}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr2 = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_pr2}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_C_U0_constant_judgement = proof_step(e, TT_PiIntro, (tt_id[]){A_U0_judgement, C_U0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id AC_pr1_nd_unreduced = proof_step(e, TT_PiElim, (tt_id[]){
            pr1_lam_B_lam_z_pi_A_sigma_xABx_judgement,
            A_C_U0_constant_judgement,
        }, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id AC_pr1_nd = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){AC_pr1_nd_unreduced}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_pr1_nd = proof_step(e, TT_PiIntro, (tt_id[]){U0_judgement, AC_pr1_nd}, 2, 0, (tt_id[]){C_U0_context}, 1, __FILE__, __LINE__);
    tt_id pr1_nd_predef = proof_step(e, TT_PiIntro, (tt_id[]){U0_judgement, A_pr1_nd}, 2, 0, (tt_id[]){A_U0_context}, 1, __FILE__, __LINE__);
    tt_id defeq_pr1_nd = proof_step(e, TT_Def, (tt_id[]){pr1_nd_predef}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr1_nd = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_pr1_nd}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id AC_pr2_nd_unreduced = proof_step(e, TT_PiElim, (tt_id[]){pr2_s2, A_C_U0_constant_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id AC_pr2_nd_midreduce = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){AC_pr2_nd_unreduced}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id AC_pr2_nd = proof_step(e, TT_BetaReduceGrossKnuth, (tt_id[]){AC_pr2_nd_midreduce}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id A_pr2_nd = proof_step(e, TT_PiIntro, (tt_id[]){U0_judgement, AC_pr2_nd}, 2, 0, (tt_id[]){C_U0_context}, 1, __FILE__, __LINE__);
    tt_id pr2_nd_predef = proof_step(e, TT_PiIntro, (tt_id[]){U0_judgement, A_pr2_nd}, 2, 0, (tt_id[]){A_U0_context}, 1, __FILE__, __LINE__);
    tt_id defeq_pr2_nd = proof_step(e, TT_Def, (tt_id[]){pr2_nd_predef}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr2_nd = proof_step(e, TT_DefEqExtL, (tt_id[]){defeq_pr2_nd}, 1, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    return (proof_tuple){{pr1, pr2, pr1_nd, pr2_nd}};
}

proof_tuple p_test_comp(tt_engine *e) {
    tt_id u0_judgement = p_define_u0(e);
    proof_tuple u0_var_contexts = proof_type_contexts(e, u0_judgement, 3);
    tt_id a_u0_context = u0_var_contexts.v[0];
    tt_id b_u0_context = u0_var_contexts.v[1];
    tt_id c_u0_context = u0_var_contexts.v[2];
    proof_tuple type_variables = proof_variables(e, u0_var_contexts);
    tt_id a_u0_judgement = type_variables.v[0];
    tt_id b_u0_judgement = type_variables.v[1];
    tt_id c_u0_judgement = type_variables.v[2];
    tt_id pi_a_b_u0_judgement = proof_step(e, TT_PiForm, (tt_id[]){a_u0_judgement, b_u0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id pi_b_c_u0_judgement = proof_step(e, TT_PiForm, (tt_id[]){b_u0_judgement, c_u0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id pi_a_c_u0_judgement = proof_step(e, TT_PiForm, (tt_id[]){a_u0_judgement, c_u0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id pi_pi_b_c_pi_a_c_u0_judgement = proof_step(e, TT_PiForm, (tt_id[]){pi_b_c_u0_judgement, pi_a_c_u0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id concrete_comp_signature_u0_judgement = proof_step(e, TT_PiForm, (tt_id[]){pi_a_b_u0_judgement, pi_pi_b_c_pi_a_c_u0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id s1_comp_signature_u0_judgement = proof_step(e, TT_PiForm, (tt_id[]){u0_judgement, concrete_comp_signature_u0_judgement}, 2, 0, (tt_id[]){c_u0_context}, 1, __FILE__, __LINE__);
    tt_id s2_comp_signature_u0_judgement = proof_step(e, TT_PiForm, (tt_id[]){u0_judgement, s1_comp_signature_u0_judgement}, 2, 0, (tt_id[]){b_u0_context}, 1, __FILE__, __LINE__);
    tt_id comp_signature_u0_judgement = proof_step(e, TT_PiForm, (tt_id[]){u0_judgement, s2_comp_signature_u0_judgement}, 2, 0, (tt_id[]){a_u0_context}, 1, __FILE__, __LINE__);
    tt_id x_a_context = proof_step(e, TT_CtxExt, (tt_id[]){a_u0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id x_a_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, x_a_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_a_b_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_a_b_u0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id f_a_b_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, f_a_b_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id f_x_b_judgement = proof_step(e, TT_PiElim, (tt_id[]){f_a_b_judgement, x_a_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id g_b_c_context = proof_step(e, TT_CtxExt, (tt_id[]){pi_b_c_u0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id g_b_c_judgement = proof_step(e, TT_Vble, (tt_id[]){0}, 0, g_b_c_context, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id g_f_x_c_judgement = proof_step(e, TT_PiElim, (tt_id[]){g_b_c_judgement, f_x_b_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id lam_x_g_f_x_a_c_judgement = proof_step(e, TT_PiIntro, (tt_id[]){a_u0_judgement, g_f_x_c_judgement}, 2, 0, (tt_id[]){x_a_context}, 1, __FILE__, __LINE__);
    tt_id lam_g_lam_x_g_f_x_a_c_judgement = proof_step(e, TT_PiIntro, (tt_id[]){pi_b_c_u0_judgement, lam_x_g_f_x_a_c_judgement}, 2, 0, (tt_id[]){g_b_c_context}, 1, __FILE__, __LINE__);
    tt_id lam_f_lam_g_lam_x_g_f_x_a_c_judgement = proof_step(e, TT_PiIntro, (tt_id[]){
            pi_a_b_u0_judgement,
            lam_g_lam_x_g_f_x_a_c_judgement,
        }, 2, 0, (tt_id[]){f_a_b_context}, 1, __FILE__, __LINE__);
    tt_id s0_comp_proof = proof_step(e, TT_PiIntro, (tt_id[]){
            u0_judgement,
            lam_f_lam_g_lam_x_g_f_x_a_c_judgement,
        }, 2, 0, (tt_id[]){c_u0_context}, 1, __FILE__, __LINE__);
    tt_id s1_comp_proof = proof_step(e, TT_PiIntro, (tt_id[]){u0_judgement, s0_comp_proof}, 2, 0, (tt_id[]){b_u0_context}, 1, __FILE__, __LINE__);
    tt_id comp_proof = proof_step(e, TT_PiIntro, (tt_id[]){u0_judgement, s1_comp_proof}, 2, 0, (tt_id[]){a_u0_context}, 1, __FILE__, __LINE__);
    return (proof_tuple){{comp_signature_u0_judgement, comp_proof}};
}

proof_tuple p_test_product_commutes(tt_engine *e) {
    tt_id u_0_judgement = p_define_u0(e);
    proof_tuple type_var_contexts = proof_type_contexts(e, u_0_judgement, 2);
    tt_id a_u0_context = type_var_contexts.v[0];
    tt_id b_u0_context = type_var_contexts.v[1];
    proof_tuple type_vars = proof_variables(e, type_var_contexts);
    tt_id a_u0_judgement = type_vars.v[0];
    tt_id b_u0_judgement = type_vars.v[1];
    tt_id a_and_b_u0_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){a_u0_judgement, b_u0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id b_and_a_u0_judgement = proof_step(e, TT_SigmaForm, (tt_id[]){b_u0_judgement, a_u0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id a_b_proposition = proof_step(e, TT_PiForm, (tt_id[]){a_and_b_u0_judgement, b_and_a_u0_judgement}, 2, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id a_proposition = proof_step(e, TT_PiForm, (tt_id[]){u_0_judgement, a_b_proposition}, 2, 0, (tt_id[]){b_u0_context}, 1, __FILE__, __LINE__);
    tt_id proposition = proof_step(e, TT_PiForm, (tt_id[]){u_0_judgement, a_proposition}, 2, 0, (tt_id[]){a_u0_context}, 1, __FILE__, __LINE__);
    proof_tuple tuple_1 = p_create_pr1_pr2(e, u_0_judgement);
    tt_id pr1_judgement = tuple_1.v[2];
    tt_id pr2_judgement = tuple_1.v[3];
    tt_id z_a_and_b_context = proof_step(e, TT_CtxExt, (tt_id[]){a_and_b_u0_judgement}, 1, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id z_a_and_b_var = proof_variable(e, z_a_and_b_context);
    tt_id pr2_a_judgement = proof_step(e, TT_PiElim, (tt_id[]){pr2_judgement, a_u0_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr2_a_b_judgement = proof_step(e, TT_PiElim, (tt_id[]){pr2_a_judgement, b_u0_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr1_a_judgement = proof_step(e, TT_PiElim, (tt_id[]){pr1_judgement, a_u0_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr1_a_b_judgement = proof_step(e, TT_PiElim, (tt_id[]){pr1_a_judgement, b_u0_judgement}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr2_z = proof_step(e, TT_PiElim, (tt_id[]){pr2_a_b_judgement, z_a_and_b_var}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr1_z = proof_step(e, TT_PiElim, (tt_id[]){pr1_a_b_judgement, z_a_and_b_var}, 2, 0, (tt_id[]){0}, 0, __FILE__, __LINE__);
    tt_id pr2_z_pr1_z_b_and_a = proof_step(e, TT_SigmaIntro, (tt_id[]){pr2_z, a_u0_judgement, pr1_z}, 3, 0, (tt_id[]){0}, 1, __FILE__, __LINE__);
    tt_id product_switch_s0_judgement = proof_step(e, TT_PiIntro, (tt_id[]){a_and_b_u0_judgement, pr2_z_pr1_z_b_and_a}, 2, 0, (tt_id[]){z_a_and_b_context}, 1, __FILE__, __LINE__);
    tt_id product_switch_s1_judgement = proof_step(e, TT_PiIntro, (tt_id[]){u_0_judgement, product_switch_s0_judgement}, 2, 0, (tt_id[]){b_u0_context}, 1, __FILE__, __LINE__);
    tt_id product_switch_proof = proof_step(e, TT_PiIntro, (tt_id[]){u_0_judgement, product_switch_s1_judgement}, 2, 0, (tt_id[]){a_u0_context}, 1, __FILE__, __LINE__);
    return (proof_tuple){{proposition, product_switch_proof}};
}
