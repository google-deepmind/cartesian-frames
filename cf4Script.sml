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
   cf0Theory cf1Theory cf2Theory

val _ = new_theory"cf4";

Definition move_def:
  move p v c = c with <| world := v;
    eval := λa e. if a ∈ c.agent ∧ e ∈ c.env then p (c.eval a e) else ARB|>
End

Theorem move_components[simp]:
  (move p v c).world = v ∧
  (move p v c).agent = c.agent ∧
  (move p v c).env = c.env ∧
  (a ∈ c.agent ∧ e ∈ c.env ⇒ (move p v c).eval a e = p (c.eval a e))
Proof
  rw[move_def]
QED

Theorem move_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ IMAGE p w ⊆ v
  ⇒
  move p v c ∈ chu_objects v
Proof
  rw[chu_objects_def, wf_def, SUBSET_DEF, PULL_EXISTS]
  \\ TRY(rw[move_def] \\ NO_TAC)
  \\ metis_tac[]
QED

Definition move_morphism_def:
  move_morphism p v m = <| dom := move p v m.dom;
                           cod := move p v m.cod;
                           map := m.map |>
End

Theorem move_morphism_components[simp]:
  (move_morphism p v m).dom = move p v m.dom ∧
  (move_morphism p v m).cod = move p v m.cod ∧
  (move_morphism p v m).map = m.map
Proof
  rw[move_morphism_def]
QED

Theorem is_chu_morphism_move[simp]:
  is_chu_morphism m.dom m.cod m.map ⇒
  is_chu_morphism (move p v m.dom) (move p v m.cod) m.map
Proof
  rw[is_chu_morphism_def]
QED

Theorem move_morphism_maps_to[simp]:
  IMAGE p w ⊆ v ∧ m :- c → d -: chu w ⇒
  (move_morphism p v m :- move p v c → move p v d -: chu v)
Proof
  simp[maps_to_in_chu]
  \\ strip_tac
  \\ metis_tac[move_in_chu_objects, is_chu_morphism_move]
QED

Definition pre_move_functor_def:
  pre_move_functor p w v =
    <| dom := chu w;
       cod := chu v;
       map := move_morphism p v |>
End

Theorem pre_move_functor_components[simp]:
  (pre_move_functor p w v).dom = chu w ∧
  (pre_move_functor p w v).cod = chu v ∧
  (pre_move_functor p w v).map = move_morphism p v
Proof
  rw[pre_move_functor_def]
QED

Theorem pre_move_functor_objf[simp]:
  c ∈ chu_objects w ∧ IMAGE p w ⊆ v ⇒
  (pre_move_functor p w v) @@ c = move p v c
Proof
  rw[objf_def, morf_def, pre_move_functor_def]
  \\ SELECT_ELIM_TAC
  \\ conj_tac
  >- (
    qexists_tac`move p v c`
    \\ simp[restrict_def, pre_chu_def]
    \\ conj_asm1_tac >- metis_tac[move_in_chu_objects]
    \\ simp[morphism_component_equality]
    \\ simp[chu_morphism_map_component_equality, chu_id_morphism_map_def] )
  \\ gen_tac \\ strip_tac
  \\ rfs[restrict_def, pre_chu_def]
  \\ rfs[morphism_component_equality]
QED

Definition move_functor_def:
  move_functor p w v = mk_functor (pre_move_functor p w v)
End

Theorem is_functor_move:
  IMAGE p w ⊆ v ⇒
  is_functor (move_functor p w v)
Proof
  rw[move_functor_def]
  \\ simp[functor_axioms_def]
  \\ simp[morf_def]
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ imp_res_tac(#1(EQ_IMP_RULE(maps_to_in_chu)))
    \\ simp[]
    \\ simp[maps_to_in_chu]
    \\ conj_tac >- metis_tac[move_in_chu_objects]
    \\ conj_tac >- metis_tac[move_in_chu_objects]
    \\ fs[is_chu_morphism_def] )
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ qexists_tac`move p v x`
    \\ conj_asm1_tac >- metis_tac[move_in_chu_objects]
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
  >- metis_tac[is_chu_morphism_move, move_in_chu_objects]
  \\ conj_asm1_tac
  >- metis_tac[is_chu_morphism_move, move_in_chu_objects]
  \\ simp[morphism_component_equality]
QED

Theorem move_functor_objf[simp]:
  c ∈ chu_objects w ∧ IMAGE p w ⊆ v ⇒
  (move_functor p w v) @@ c = move p v c
Proof
  rw[move_functor_def]
QED

Theorem move_functor_morf[simp]:
  m ∈ (pre_chu w).mor ⇒
  (move_functor p w v) ## m = move_morphism p v m
Proof
  rw[move_functor_def, mk_functor_def, morf_def, restrict_def]
QED

Theorem move_sum:
  move p v (sum c d) = sum (move p v c) (move p v d)
Proof
  rw[cf_component_equality, sum_def]
  \\ simp[mk_cf_def, FUN_EQ_THM, EXISTS_PROD]
  \\ rw[] \\ rw[]
  \\ simp[sum_eval_def]
  \\ rw[move_def, EXISTS_PROD] \\ rw[] \\ fs[]
QED

Theorem move_prod:
  move p v (prod c d) = prod (move p v c) (move p v d)
Proof
  rw[cf_component_equality, prod_def]
  \\ simp[mk_cf_def, FUN_EQ_THM, EXISTS_PROD]
  \\ rw[] \\ rw[]
  \\ simp[sum_eval_def]
  \\ rw[move_def, EXISTS_PROD] \\ rw[] \\ fs[]
QED

Theorem move_swap:
  move p v (swap c) = swap (move p v c)
Proof
  rw[cf_component_equality]
  \\ rw[swap_def, move_def, FUN_EQ_THM]
  \\ rw[] \\ fs[]
QED

Theorem move_cf0[simp]:
  move p v (cf0 w) = cf0 v
Proof
  rw[cf_component_equality, cf0_def]
  \\ rw[FUN_EQ_THM, move_def]
QED

Theorem move_cfT[simp]:
  move p v (cfT w) = cfT v
Proof
  rw[cf_component_equality, cfT_def, cf0_def]
  \\ rw[FUN_EQ_THM, move_def]
QED

Theorem move_null[simp]:
  move p v (null w) = null v
Proof
  rw[cf_component_equality, null_def]
  \\ rw[FUN_EQ_THM, move_def]
QED

(* TODO: proof about getting cf1 and cfbot from 1 and ⊥ via functors? *)

Theorem homotopy_equiv_move:
  IMAGE p w ⊆ v ∧ c ≃ d -: w ⇒ move p v c ≃ move p v d -: v
Proof
  rw[homotopy_equiv_def]
  \\ qexists_tac`move_morphism p v f`
  \\ qexists_tac`move_morphism p v g`
  \\ conj_asm1_tac >- metis_tac[move_morphism_maps_to]
  \\ conj_asm1_tac >- metis_tac[move_morphism_maps_to]
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

Theorem ensure_move:
  IMAGE p w ⊆ v ∧ s ⊆ w ∧ s ∈ ensure c ⇒ IMAGE p s ∈ ensure (move p v c)
Proof
  rw[ensure_def, SUBSET_DEF, PULL_EXISTS]
  \\ rw[move_def]
  \\ metis_tac[]
QED

Theorem ensure_ctrl_move_iff:
  IMAGE p w ⊆ v ∧ c ∈ chu_objects w ∧ s ⊆ w ∧ t ⊆ v ∧ (∀x. x ∈ w ⇒ (p x ∈ t ⇔  x ∈ s)) ⇒
    (s ∈ ensure c ⇔ t ∈ ensure (move p v c)) ∧
    (s ∈ ctrl c ⇔ t ∈ ctrl (move p v c))
Proof
  rw[ensure_def, ctrl_def, prevent_def, SUBSET_DEF, PULL_EXISTS, EQ_IMP_THM,
     chu_objects_def, wf_def, move_def]
  \\ metis_tac[]
QED

val _ = export_theory();
