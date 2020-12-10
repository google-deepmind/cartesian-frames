(*
Copyright 2020 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

open HolKernel boolLib bossLib Parse dep_rewrite
   listTheory rich_listTheory alistTheory pairTheory
   pred_setTheory categoryTheory functorTheory
   cf0Theory cf1Theory cf2Theory cf3Theory

val _ = new_theory"cf4";

Definition move_fn_def:
  move_fn p v c = c with <| world := v;
    eval := λa e. if a ∈ c.agent ∧ e ∈ c.env then p (c.eval a e) else ARB|>
End

Theorem move_fn_components[simp]:
  (move_fn p v c).world = v ∧
  (move_fn p v c).agent = c.agent ∧
  (move_fn p v c).env = c.env ∧
  (a ∈ c.agent ∧ e ∈ c.env ⇒ (move_fn p v c).eval a e = p (c.eval a e))
Proof
  rw[move_fn_def]
QED

Theorem move_fn_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ IMAGE p w ⊆ v
  ⇒
  move_fn p v c ∈ chu_objects v
Proof
  rw[chu_objects_def, wf_def, SUBSET_DEF, PULL_EXISTS]
  \\ TRY(rw[move_fn_def] \\ NO_TAC)
  \\ metis_tac[]
QED

Definition move_fn_morphism_def:
  move_fn_morphism p v m = <| dom := move_fn p v m.dom;
                           cod := move_fn p v m.cod;
                           map := m.map |>
End

Theorem move_fn_morphism_components[simp]:
  (move_fn_morphism p v m).dom = move_fn p v m.dom ∧
  (move_fn_morphism p v m).cod = move_fn p v m.cod ∧
  (move_fn_morphism p v m).map = m.map
Proof
  rw[move_fn_morphism_def]
QED

Theorem is_chu_morphism_move_fn[simp]:
  is_chu_morphism m.dom m.cod m.map ⇒
  is_chu_morphism (move_fn p v m.dom) (move_fn p v m.cod) m.map
Proof
  rw[is_chu_morphism_def]
QED

Theorem move_fn_morphism_maps_to[simp]:
  IMAGE p w ⊆ v ∧ m :- c → d -: chu w ⇒
  (move_fn_morphism p v m :- move_fn p v c → move_fn p v d -: chu v)
Proof
  simp[maps_to_in_chu]
  \\ strip_tac
  \\ metis_tac[move_fn_in_chu_objects, is_chu_morphism_move_fn]
QED

Definition pre_move_fn_functor_def:
  pre_move_fn_functor p w v =
    <| dom := chu w;
       cod := chu v;
       map := move_fn_morphism p v |>
End

Theorem pre_move_fn_functor_components[simp]:
  (pre_move_fn_functor p w v).dom = chu w ∧
  (pre_move_fn_functor p w v).cod = chu v ∧
  (pre_move_fn_functor p w v).map = move_fn_morphism p v
Proof
  rw[pre_move_fn_functor_def]
QED

Theorem pre_move_fn_functor_objf[simp]:
  c ∈ chu_objects w ∧ IMAGE p w ⊆ v ⇒
  (pre_move_fn_functor p w v) @@ c = move_fn p v c
Proof
  rw[objf_def, morf_def, pre_move_fn_functor_def]
  \\ SELECT_ELIM_TAC
  \\ conj_tac
  >- (
    qexists_tac`move_fn p v c`
    \\ simp[restrict_def, pre_chu_def]
    \\ conj_asm1_tac >- metis_tac[move_fn_in_chu_objects]
    \\ simp[morphism_component_equality]
    \\ simp[chu_morphism_map_component_equality, chu_id_morphism_map_def] )
  \\ gen_tac \\ strip_tac
  \\ rfs[restrict_def, pre_chu_def]
  \\ rfs[morphism_component_equality]
QED

Definition move_fn_functor_def:
  move_fn_functor p w v = mk_functor (pre_move_fn_functor p w v)
End

Theorem is_functor_move_fn:
  IMAGE p w ⊆ v ⇒
  is_functor (move_fn_functor p w v)
Proof
  rw[move_fn_functor_def]
  \\ simp[functor_axioms_def]
  \\ simp[morf_def]
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ imp_res_tac(#1(EQ_IMP_RULE(maps_to_in_chu)))
    \\ simp[]
    \\ simp[maps_to_in_chu]
    \\ conj_tac >- metis_tac[move_fn_in_chu_objects]
    \\ conj_tac >- metis_tac[move_fn_in_chu_objects]
    \\ fs[is_chu_morphism_def] )
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ qexists_tac`move_fn p v x`
    \\ conj_asm1_tac >- metis_tac[move_fn_in_chu_objects]
    \\ simp[morphism_component_equality]
    \\ simp[chu_morphism_map_component_equality, chu_id_morphism_map_def] )
  \\ rpt gen_tac \\ strip_tac
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ DEP_REWRITE_TAC[chu_comp]
  \\ simp[]
  \\ fs[composable_in_def]
  \\ fs[pre_chu_def]
  \\ conj_asm1_tac
  >- metis_tac[is_chu_morphism_move_fn, move_fn_in_chu_objects]
  \\ conj_asm1_tac
  >- metis_tac[is_chu_morphism_move_fn, move_fn_in_chu_objects]
  \\ simp[morphism_component_equality]
QED

Theorem move_fn_functor_objf[simp]:
  c ∈ chu_objects w ∧ IMAGE p w ⊆ v ⇒
  (move_fn_functor p w v) @@ c = move_fn p v c
Proof
  rw[move_fn_functor_def]
QED

Theorem move_fn_functor_morf[simp]:
  m ∈ (pre_chu w).mor ⇒
  (move_fn_functor p w v) ## m = move_fn_morphism p v m
Proof
  rw[move_fn_functor_def, mk_functor_def, morf_def, restrict_def]
QED

Theorem image_move_fn:
  image (move_fn p v c) = IMAGE p (image c)
Proof
  rw[image_def, move_fn_def, EXTENSION, PULL_EXISTS]
  \\ metis_tac[]
QED

Theorem move_fn_sum:
  move_fn p v (sum c d) = sum (move_fn p v c) (move_fn p v d)
Proof
  rw[cf_component_equality, sum_def]
  \\ simp[mk_cf_def, FUN_EQ_THM, EXISTS_PROD]
  \\ rw[] \\ rw[]
  \\ simp[sum_eval_def]
  \\ rw[move_fn_def, EXISTS_PROD] \\ rw[] \\ fs[]
QED

Theorem move_fn_prod:
  move_fn p v (prod c d) = prod (move_fn p v c) (move_fn p v d)
Proof
  rw[cf_component_equality, prod_def]
  \\ simp[mk_cf_def, FUN_EQ_THM, EXISTS_PROD]
  \\ rw[] \\ rw[]
  \\ simp[sum_eval_def]
  \\ rw[move_fn_def, EXISTS_PROD] \\ rw[] \\ fs[]
QED

Theorem move_fn_swap:
  move_fn p v (swap c) = swap (move_fn p v c)
Proof
  rw[cf_component_equality]
  \\ rw[swap_def, move_fn_def, FUN_EQ_THM]
  \\ rw[] \\ fs[]
QED

Theorem move_fn_cf0[simp]:
  move_fn p v (cf0 w) = cf0 v
Proof
  rw[cf_component_equality, cf0_def]
  \\ rw[FUN_EQ_THM, move_fn_def]
QED

Theorem move_fn_cfT[simp]:
  move_fn p v (cfT w) = cfT v
Proof
  rw[cf_component_equality, cfT_def, cf0_def]
  \\ rw[FUN_EQ_THM, move_fn_def]
QED

Theorem move_fn_null[simp]:
  move_fn p v (null w) = null v
Proof
  rw[cf_component_equality, null_def]
  \\ rw[FUN_EQ_THM, move_fn_def]
QED

(* TODO: proof about getting cf1 and cfbot from 1 and ⊥ via functors? *)

Theorem homotopy_equiv_move_fn:
  IMAGE p w ⊆ v ∧ c ≃ d -: w ⇒ move_fn p v c ≃ move_fn p v d -: v
Proof
  rw[homotopy_equiv_def]
  \\ qexists_tac`move_fn_morphism p v f`
  \\ qexists_tac`move_fn_morphism p v g`
  \\ conj_asm1_tac >- metis_tac[move_fn_morphism_maps_to]
  \\ conj_asm1_tac >- metis_tac[move_fn_morphism_maps_to]
  \\ rpt(qhdtm_x_assum`homotopic`mp_tac)
  \\ imp_res_tac(#1(EQ_IMP_RULE maps_to_in_chu))
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ simp[]
  \\ DEP_REWRITE_TAC[chu_comp]
  \\ simp[homotopic_def, pre_chu_def, hom_comb_def]
  \\ fs[]
  \\ simp[chu_id_morphism_map_def]
  \\ simp[is_chu_morphism_def]
  \\ simp[composable_in_def, pre_chu_def]
QED

Theorem ensure_move_fn:
  IMAGE p w ⊆ v ∧ s ⊆ w ∧ s ∈ ensure c ⇒ IMAGE p s ∈ ensure (move_fn p v c)
Proof
  rw[ensure_def, SUBSET_DEF, PULL_EXISTS]
  \\ rw[move_fn_def]
  \\ metis_tac[]
QED

Theorem ensure_ctrl_move_fn_iff:
  IMAGE p w ⊆ v ∧ c ∈ chu_objects w ∧ s ⊆ w ∧ t ⊆ v ∧ (∀x. x ∈ w ⇒ (p x ∈ t ⇔  x ∈ s)) ⇒
    (s ∈ ensure c ⇔ t ∈ ensure (move_fn p v c)) ∧
    (s ∈ ctrl c ⇔ t ∈ ctrl (move_fn p v c))
Proof
  rw[ensure_def, ctrl_def, prevent_def, SUBSET_DEF, PULL_EXISTS, EQ_IMP_THM,
     chu_objects_def, wf_def, move_fn_def]
  \\ metis_tac[]
QED

Theorem obs_move_fn:
  IMAGE p w ⊆ v ∧ c ∈ chu_objects w ∧ s ⊆ w ∧ t ⊆ v ∧ (∀x. x ∈ w ⇒ (p x ∈ t ⇔ x ∈ s)) ∧ s ∈ obs c ⇒
  t ∈ obs (move_fn p v c)
Proof
  strip_tac
  \\ rfs[UNDISCH(obs_homotopy_equiv_prod)]
  \\ imp_res_tac homotopy_equiv_move_fn
  \\ fs[move_fn_prod]
  \\ DEP_REWRITE_TAC[Q.SPEC`v`(Q.GEN`w`obs_homotopy_equiv_prod)]
  \\ simp[]
  \\ conj_asm1_tac >- metis_tac[move_fn_in_chu_objects]
  \\ map_every qexists_tac[`move_fn p v c1`, `move_fn p v c2`]
  \\ conj_asm1_tac >- metis_tac[move_fn_in_chu_objects]
  \\ conj_asm1_tac >- metis_tac[move_fn_in_chu_objects]
  \\ simp[image_move_fn]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
QED

Definition move_def:
  move c d = mk_cf
    <| world := c.world;
       agent := d.agent;
       env := IMAGE encode_pair (d.env × c.env);
       eval := λa e. c.eval (d.eval a (FST (decode_pair e))) (SND (decode_pair e)) |>
End

Theorem move_components[simp]:
  (move c d).world = c.world ∧
  (move c d).agent = d.agent ∧
  (move c d).env = IMAGE encode_pair (d.env × c.env) ∧
  (∀a p. a ∈ d.agent ∧ FST p ∈ d.env ∧ SND p ∈ c.env ⇒
    (move c d).eval a (encode_pair p) = c.eval (d.eval a (FST p)) (SND p))
Proof
  rw[move_def] \\ rw[mk_cf_def]
QED

Theorem move_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ d ∈ chu_objects v ∧ c.agent = v ⇒
  move c d ∈ chu_objects w
Proof
  rw[chu_objects_def]
  \\ fs[wf_def, PULL_EXISTS]
  \\ rw[move_def, mk_cf_def]
  \\ rw[] \\ fs[]
QED

Definition move_morphism_map_def:
  move_morphism_map m =
    <| map_agent := m.map_agent;
       map_env := λp. encode_pair (m.map_env (FST (decode_pair p)), SND (decode_pair p)) |>
End

Definition move_morphism_def:
  move_morphism c m =
    mk_chu_morphism (move c m.dom) (move c m.cod)
      (move_morphism_map m.map)
End

Theorem move_morphism_components[simp]:
  (move_morphism c m).dom = move c m.dom ∧
  (move_morphism c m).cod = move c m.cod
Proof
  rw[move_morphism_def]
QED

Theorem is_chu_morphism_move[simp]:
  is_chu_morphism m.dom m.cod m.map ⇒
  is_chu_morphism (move c m.dom) (move c m.cod) (move_morphism c m).map
Proof
  rw[is_chu_morphism_def]
  \\ rw[move_morphism_def, mk_chu_morphism_def, move_morphism_map_def]
  \\ fs[extensional_def, FORALL_PROD, restrict_def]
QED

Theorem move_morphism_maps_to[simp]:
  x ∈ chu_objects w ∧ x.agent = v ∧ m :- c → d -: chu v ⇒
  (move_morphism x m :- move x c → move x d -: chu w)
Proof
  simp[maps_to_in_chu]
  \\ strip_tac
  \\ metis_tac[is_chu_morphism_move]
QED

Definition pre_move_functor_def:
  pre_move_functor c = <| dom := chu c.agent; cod := chu c.world; map := move_morphism c |>
End

Theorem pre_move_functor_components[simp]:
  (pre_move_functor c).dom = chu c.agent ∧
  (pre_move_functor c).cod = chu c.world ∧
  (pre_move_functor c).map = move_morphism c
Proof
  rw[pre_move_functor_def]
QED

Theorem pre_move_functor_objf[simp]:
  c ∈ chu_objects w ∧ d ∈ chu_objects v ∧ c.agent = v ⇒
  (pre_move_functor c) @@ d = move c d
Proof
  rw[objf_def, morf_def, pre_move_functor_def]
  \\ SELECT_ELIM_TAC
  \\ `c.world = w` by fs[chu_objects_def]
  \\ conj_tac
  >- (
    qexists_tac`move c d`
    \\ conj_asm1_tac >- metis_tac[move_in_chu_objects]
    \\ simp[morphism_component_equality, move_morphism_def, mk_chu_morphism_def]
    \\ simp[chu_morphism_map_component_equality, chu_id_morphism_map_def]
    \\ simp[restrict_def, FUN_EQ_THM, move_morphism_map_def]
    \\ rw[] \\ rw[] \\ fs[])
  \\ gen_tac \\ strip_tac
  \\ rfs[morphism_component_equality]
QED

Definition move_functor_def:
  move_functor c = mk_functor (pre_move_functor c)
End

Theorem is_functor_move:
  c ∈ chu_objects w ⇒
  is_functor (move_functor c)
Proof
  rw[move_functor_def]
  \\ simp[functor_axioms_def]
  \\ simp[morf_def]
  \\ `c.world = w` by fs[chu_objects_def]
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ imp_res_tac(#1(EQ_IMP_RULE(maps_to_in_chu)))
    \\ DEP_REWRITE_TAC[Q.GEN`v`pre_move_functor_objf]
    \\ simp[])
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ qexists_tac`move c x`
    \\ simp[morphism_component_equality]
    \\ simp[chu_morphism_map_component_equality, chu_id_morphism_map_def]
    \\ simp[move_morphism_def, mk_chu_morphism_def, restrict_def, FUN_EQ_THM]
    \\ rw[chu_id_morphism_map_def, restrict_def, move_morphism_map_def]
    \\ fs[])
  \\ rpt gen_tac \\ strip_tac
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ DEP_REWRITE_TAC[chu_comp]
  \\ simp[]
  \\ fs[composable_in_def]
  \\ fs[pre_chu_def]
  \\ conj_asm1_tac >- metis_tac[is_chu_morphism_move]
  \\ conj_asm1_tac >- metis_tac[is_chu_morphism_move]
  \\ simp[morphism_component_equality]
  \\ simp[move_morphism_def, mk_chu_morphism_def, move_morphism_map_def]
  \\ simp[restrict_def, FUN_EQ_THM]
  \\ rw[]
  \\ fs[is_chu_morphism_def]
  \\ metis_tac[]
QED

Theorem move_functor_objf[simp]:
  c ∈ chu_objects w ∧ d ∈ chu_objects v ∧ c.agent = v ⇒
  (move_functor c) @@ d = move c d
Proof
  rw[move_functor_def]
  \\ metis_tac[pre_move_functor_objf]
QED

Theorem move_fn_functor_morf[simp]:
  m ∈ (pre_chu v).mor ∧ c.agent = v ⇒
  (move_functor c) ## m = move_morphism c m
Proof
  rw[move_functor_def, mk_functor_def, morf_def, restrict_def]
QED

Theorem move_cfT[simp]:
  move c (cfT w) = cfT c.world
Proof
  rw[move_def, mk_cf_def, cf_component_equality, cfT_def, cf0_def]
  \\ rw[swap_def, FUN_EQ_THM]
QED

Theorem move_null[simp]:
  move c (null w) = null c.world
Proof
  rw[move_def, null_def, mk_cf_def, FUN_EQ_THM]
QED

(* we don't have equality here because our encodings
   of sums and products do not commute *)
Theorem move_prod:
  c ∈ chu_objects w ∧ d1 ∈ chu_objects v ∧ d2 ∈ chu_objects v ∧ c.agent = v ⇒
  move c (d1 && d2) ≅ move c d1 && move c d2 -: chu w
Proof
  rw[iso_objs_thm]
  \\ rw[maps_to_in_chu]
  \\ qexists_tac`mk_chu_morphism (move c (d1 && d2)) (move c d1 && move c d2)
                   <| map_agent := I;
                      map_env := λx.
                        sum_CASE (decode_sum x)
                          (λp. encode_pair (encode_sum(INL(FST(decode_pair p))),
                                            SND(decode_pair p)))
                          (λp. encode_pair (encode_sum(INR(FST(decode_pair p))),
                                            SND(decode_pair p))) |>`
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    simp[mk_chu_morphism_def, is_chu_morphism_def]
    \\ simp[prod_def, restrict_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD]
    \\ rw[move_def, mk_cf_def, restrict_def] \\ rw[sum_eval_def] \\ fs[] )
  \\ simp[chu_iso_bij]
  \\ simp[mk_chu_morphism_def]
  \\ simp[prod_def, restrict_def, PULL_EXISTS]
  \\ conj_tac >- ( simp[BIJ_IFF_INV] \\ qexists_tac`I` \\ simp[] )
  \\ simp[BIJ_IFF_INV, PULL_EXISTS, EXISTS_PROD]
  \\ qexists_tac`λp. sum_CASE (decode_sum(FST(decode_pair p)))
                              (λx. encode_sum(INL(encode_pair(x, SND(decode_pair p)))))
                              (λx. encode_sum(INR(encode_pair(x, SND(decode_pair p)))))`
  \\ rw[] \\ fs[]
QED

Theorem homotopy_equiv_move:
  c ∈ chu_objects w ∧ c.agent = v ∧
  d1 ≃ d2 -: v ⇒ move c d1 ≃ move c d2 -: w
Proof
  rw[homotopy_equiv_def]
  \\ qexists_tac`move_morphism c f`
  \\ qexists_tac`move_morphism c g`
  \\ simp[]
  \\ ntac 4 (pop_assum mp_tac)
  \\ simp[AND_IMP_INTRO]
  \\ qho_match_abbrev_tac`A f g d1 d2 ⇒ Q f g d1 d2 ∧ Q g f d2 d1`
  \\ map_every qid_spec_tac[`f`,`g`,`d1`,`d2`]
  \\ `∀f g d1 d2. A f g d1 d2 ⇒ Q f g d1 d2` suffices_by ( rw[Abbr`A`, Abbr`Q`] \\ metis_tac[] )
  \\ rw[Abbr`A`, Abbr`Q`]
  \\ first_assum(mp_then Any (qspecl_then[`c`,`w`]mp_tac) move_morphism_maps_to)
  \\ last_assum(mp_then Any (qspecl_then[`c`,`w`]mp_tac) move_morphism_maps_to)
  \\ impl_tac >- simp[] \\ strip_tac
  \\ impl_tac >- simp[] \\ strip_tac
  \\ imp_res_tac maps_to_comp \\ fs[]
  \\ imp_res_tac (#1(EQ_IMP_RULE maps_to_in_chu))
  \\ rpt (qhdtm_x_assum`homotopic`mp_tac)
  \\ simp[homotopic_def, pre_chu_def]
  \\ simp[hom_comb_def]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ DEP_REWRITE_TAC[chu_comp]
  \\ simp[CONJ_ASSOC]
  \\ conj_tac
  >- (simp[composable_in_def, pre_chu_def]
      \\ metis_tac[is_chu_morphism_move])
  \\ simp[pre_chu_def]
  \\ fs[is_chu_morphism_def, EXISTS_PROD, PULL_EXISTS, restrict_def]
  \\ rw[] \\ fs[chu_id_morphism_map_def]
  \\ fs[restrict_def, extensional_def]
  \\ fs[move_morphism_def, mk_chu_morphism_def, restrict_def, move_morphism_map_def]
QED

Definition encode_list_def:
  encode_list [] = "" ∧
  encode_list (h::t) = encode_pair (h, encode_list t)
End

Definition decode_list_def:
  decode_list s =
    if NULL s then [] else
    FST (decode_pair s) :: decode_list (SND (decode_pair s))
Termination
  WF_REL_TAC`measure LENGTH`
  \\ reverse(rw[decode_pair_def, UNCURRY, NULL_EQ])
  >- ( Cases_on`s` \\ fs[] )
  \\ qmatch_goalsub_abbrev_tac`SPLITP P s`
  \\ qspec_then`s`(SUBST1_TAC o GSYM) SPLITP_LENGTH
  \\ Cases_on`SND (SPLITP P s)` \\ fs[]
  \\ Cases_on`SPLITP P s` \\ rfs[]
  \\ fs[SPLITP_NIL_SND_EVERY]
  \\ Cases_on`s` \\ fs[]
End

Theorem decode_encode_list[simp]:
  decode_list (encode_list l) = l
Proof
  Induct_on`l`
  \\ simp[Once decode_list_def, encode_list_def]
  \\ rw[]
  \\ fs[encode_pair_def]
QED

Definition encode_function_def:
  encode_function d f =
  encode_list (MAP (λx. encode_pair (x, f x)) (SET_TO_LIST d))
End

Definition decode_function_def:
  decode_function s =
    λx. option_CASE (ALOOKUP (MAP decode_pair (decode_list s)) x) ARB I
End

Theorem decode_encode_function[simp]:
  FINITE d ∧ extensional f d ⇒
  decode_function (encode_function d f) = f
Proof
  rw[decode_function_def, FUN_EQ_THM, extensional_def]
  \\ rw[encode_function_def, MAP_MAP_o, combinTheory.o_DEF]
  \\ qmatch_goalsub_abbrev_tac`ALOOKUP ls x`
  \\ Cases_on`ALOOKUP ls x` \\ simp[]
  >- ( fs[ALOOKUP_FAILS, Abbr`ls`, MEM_MAP] \\ rfs[] )
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[Abbr`ls`, MEM_MAP]
QED

Definition cf_def:
  cf p e w = mk_cf
    <| world := w; agent := IMAGE (encode_function e) p;
       env := e; eval := decode_function |>
End

Theorem cf_components[simp]:
  (cf p e w).world = w ∧
  (cf p e w).agent = IMAGE (encode_function e) p ∧
  (cf p e w).env = e
Proof
  rw[cf_def]
QED

Theorem cf_in_chu_objects:
  FINITE e ∧ (∀f. f ∈ p ⇒extensional f e ∧ IMAGE f e ⊆ w) ⇒
  cf p e w ∈ chu_objects w
Proof
  rw[chu_objects_def]
  \\ rw[wf_def, cf_def, mk_cf_def] \\ rw[]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[decode_encode_function]
QED

Theorem exists_homotopy_equiv_cf:
  c ∈ chu_objects w ∧ FINITE e ∧ c.env = e ⇒
  ∃p. (∀f. f ∈ p ⇒ extensional f e ∧ IMAGE f e ⊆ w) ∧
      c ≃ cf p e w -: w
Proof
  rw[]
  \\ qexists_tac`{f | extensional f c.env ∧ IMAGE f c.env ⊆ w ∧
                      ∃a. a ∈ c.agent ∧ ∀e. e ∈ c.env ⇒ f e = c.eval a e}`
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`cf p e`
  \\ `cf p e w ∈ chu_objects w` by ( irule cf_in_chu_objects \\ simp[Abbr`p`] )
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism c (cf p e w)
                   <| map_agent := encode_function c.env o c.eval; map_env := I |>`
  \\ qexists_tac`mk_chu_morphism (cf p e w) c
                   <| map_agent := λf. @a. a ∈ c.agent ∧
                                           ∀e. e ∈ c.env ⇒ decode_function f e = c.eval a e;
                      map_env := I |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[cf_def, mk_cf_def]
    \\ simp[Abbr`p`]
    \\ conj_asm1_tac
    >- (
      fs[chu_objects_def, wf_def]
      \\ rw[]
      \\ qexists_tac`c.eval a`
      \\ simp[extensional_def, SUBSET_DEF, PULL_EXISTS]
      \\ metis_tac[] )
    \\ rw[]
    \\ DEP_REWRITE_TAC[decode_encode_function]
    \\ fs[chu_objects_def, wf_def]
    \\ rw[extensional_def] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def, PULL_EXISTS]
    \\ CONV_TAC(RAND_CONV(SWAP_FORALL_CONV))
    \\ simp[GSYM FORALL_AND_THM]
    \\ gen_tac
    \\ Cases_on`x ∈ p` \\ simp[]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ DEP_REWRITE_TAC[decode_encode_function]
    \\ conj_asm1_tac >- fs[Abbr`p`]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- (fs[Abbr`p`] \\ metis_tac[])
    \\ rw[]
    \\ simp[cf_def, mk_cf_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ DEP_REWRITE_TAC[decode_encode_function]
    \\ conj_tac >- (fs[Abbr`p`] \\ metis_tac[])
    \\ fs[Abbr`p`]
    \\ metis_tac[decode_encode_function] )
  \\ qmatch_goalsub_abbrev_tac`f o g -: _`
  \\ imp_res_tac maps_to_comp \\ fs[]
  \\ conj_tac
  \\ irule homotopic_id
  \\ fs[maps_to_in_chu, pre_chu_def]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ DEP_REWRITE_TAC[chu_comp]
  \\ simp[composable_in_def, pre_chu_def]
  \\ simp[Abbr`f`, Abbr`g`, mk_chu_morphism_def]
  \\ simp[restrict_def]
QED

Definition cf_swap_def:
  cf_swap p a w = mk_cf
    <| world := w; agent := a; env := IMAGE (encode_function a) p;
       eval := flip decode_function |>
End

Theorem cf_swap_components[simp]:
  (cf_swap p a w).world = w ∧
  (cf_swap p a w).env = IMAGE (encode_function a) p ∧
  (cf_swap p a w).agent = a
Proof
  rw[cf_swap_def]
QED

Theorem cf_swap_swap_cf:
  swap (cf p x w) = cf_swap p x w
Proof
  rw[cf_component_equality]
  \\ rw[cf_def, cf_swap_def]
  \\ rw[mk_cf_def, swap_def, FUN_EQ_THM]
  \\ rw[] \\ fs[]
  \\ metis_tac[]
QED

(* again for both of these we have isomorphism instead
   of equality because of encodings *)

Theorem move_fn_move_cf:
  c ∈ chu_objects v ∧ IMAGE p v ⊆ w ∧ FINITE v ∧ extensional p v ⇒
  move_fn p w c ≅ move (cf_swap {p} v w) c -: chu w
Proof
  rw[iso_objs_thm]
  \\ qexists_tac`mk_chu_morphism (move_fn p w c) (move (cf_swap {p} v w) c)
                 <| map_agent := I; map_env := FST o decode_pair |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ DEP_REWRITE_TAC[Q.GENL[`w`,`v`]move_fn_in_chu_objects]
    \\ DEP_REWRITE_TAC[move_in_chu_objects]
    \\ simp[GSYM cf_swap_swap_cf]
    \\ DEP_REWRITE_TAC[cf_in_chu_objects]
    \\ simp[]
    \\ conj_tac >- metis_tac[]
    \\ simp[mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[restrict_def]
    \\ simp[cf_def, mk_cf_def]
    \\ fs[chu_objects_def, wf_def]
    \\ rw[] )
  \\ simp[chu_iso_bij]
  \\ fs[maps_to_in_chu]
  \\ simp[BIJ_IFF_INV, mk_chu_morphism_def, PULL_EXISTS, EXISTS_PROD]
  \\ rw[restrict_def]
  \\ qexists_tac`I` \\ rw[]
  \\ qexists_tac`λx. encode_pair (x, encode_function v p)`
  \\ rw[]
QED

Theorem move_fn_move_cf_sing:
  c ∈ chu_objects w ∧ d ∈ chu_objects v ∧ c.agent = v ∧ c.env = {e} ⇒
  move c d ≅ move_fn (flip c.eval e) w d -: chu w
Proof
  rw[iso_objs_thm]
  \\ qexists_tac`mk_chu_morphism (move c d) (move_fn (flip c.eval e) w d)
       <| map_agent := I; map_env := λx. encode_pair (x, e) |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ conj_asm1_tac
    >- (
      irule move_fn_in_chu_objects
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ fs[chu_objects_def, wf_def, SUBSET_DEF, PULL_EXISTS]
      \\ fs[] )
    \\ simp[mk_chu_morphism_def, is_chu_morphism_def]
    \\ simp[move_def, move_fn_def, mk_cf_def]
    \\ simp[restrict_def, PULL_EXISTS, EXISTS_PROD] )
  \\ simp[chu_iso_bij]
  \\ fs[maps_to_in_chu]
  \\ simp[BIJ_IFF_INV, PULL_EXISTS, EXISTS_PROD, mk_chu_morphism_def]
  \\ map_every qexists_tac[`I`, `FST o decode_pair`]
  \\ simp[restrict_def]
QED

Theorem move_SURJ_inverse:
  SURJ p w v ∧ extensional p w ∧ c ∈ chu_objects v ∧ FINITE v ∧
    Q = {q | extensional q v ∧ IMAGE q v ⊆ w ∧ restrict (p o q) v = restrict I v}⇒
  move_fn p v (move (cf_swap Q v w) c) ≃ c -: v
Proof
  rw[]
  \\ qmatch_goalsub_abbrev_tac`cf_swap Q`
  \\ rw[homotopy_equiv_def]
  \\ qmatch_goalsub_abbrev_tac`_ :- z → c -: chu v`
  \\ `∃q. q ∈ Q`
  by (
    simp[Abbr`Q`, FUN_EQ_THM, restrict_def]
    \\ fs[SURJ_DEF]
    \\ Cases_on`v = ∅` \\ fs[]
    >- (
      simp[extensional_def]
      \\ qexists_tac`K ARB`
      \\ simp[] )
    \\ qexists_tac`restrict (λx. (@y. y ∈ w ∧ p y = x )) v`
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ simp[restrict_def]
    \\ simp[GSYM FORALL_AND_THM]
    \\ gen_tac
    \\ Cases_on`x ∈ v` \\ simp[]
    \\ SELECT_ELIM_TAC \\ simp[])
  \\ qexists_tac`mk_chu_morphism z c <| map_agent := I;
                                        map_env := λe. encode_pair (e, encode_function v q) |>`
  \\ qexists_tac`mk_chu_morphism c z <| map_agent := I; map_env := FST o decode_pair |>`
  \\ `z ∈ chu_objects v`
  by (
    simp[Abbr`z`]
    \\ irule move_fn_in_chu_objects
    \\ qexists_tac`w`
    \\ conj_tac
    >- (
      irule move_in_chu_objects
      \\ simp[]
      \\ simp[GSYM cf_swap_swap_cf]
      \\ irule cf_in_chu_objects
      \\ simp[Abbr`Q`] )
    \\ fs[SURJ_DEF, SUBSET_DEF, PULL_EXISTS] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`z`]
    \\ conj_tac >- metis_tac[]
    \\ simp[move_fn_def, GSYM cf_swap_swap_cf, cf_def, mk_cf_def]
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ DEP_REWRITE_TAC[decode_encode_function]
    \\ fs[Abbr`Q`, restrict_def, FUN_EQ_THM]
    \\ fs[chu_objects_def, wf_def, SUBSET_DEF, PULL_EXISTS]
    \\ fs[]
    \\ metis_tac[] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`z`, PULL_EXISTS, EXISTS_PROD]
    \\ simp[GSYM cf_swap_swap_cf]
    \\ simp[cf_def, mk_cf_def]
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC >- (
      fs[chu_objects_def, wf_def, SUBSET_DEF, PULL_EXISTS]
      \\ metis_tac[] )
    \\ DEP_REWRITE_TAC[decode_encode_function]
    \\ fs[Abbr`Q`, restrict_def, FUN_EQ_THM]
    \\ metis_tac[] )
  \\ imp_res_tac maps_to_comp \\ fs[]
  \\ conj_tac
  \\ irule homotopic_id
  \\ fs[maps_to_in_chu, pre_chu_def]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ DEP_REWRITE_TAC[chu_comp]
  \\ simp[composable_in_def, pre_chu_def]
  \\ simp[mk_chu_morphism_def]
  \\ simp[restrict_def]
  \\ simp[Abbr`z`]
QED

val _ = export_theory();
