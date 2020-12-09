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
   pairTheory pred_setTheory categoryTheory functorTheory
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

val _ = export_theory();
