(*
Copyright 2021 DeepMind Technologies Limited.

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
  pairTheory pred_setTheory categoryTheory
  cf0Theory cf1Theory cf2Theory cf4Theory cf5Theory cf6Theory

val _ = new_theory"cf7";

Definition is_subsum_def:
  is_subsum c d s ⇔
    s.world = (sum c d).world ∧
    s.agent = (sum c d).agent ∧
    s.env ⊆ (sum c d).env ∧
    (∀a. s.eval a = restrict ((sum c d).eval a) s.env) ∧
    c ≃ (mk_cf <| world := c.world;
                  agent := IMAGE (encode_sum o INL) c.agent;
                  env := s.env;
                  eval := s.eval |>) -: c.world ∧
    d ≃ (mk_cf <| world := d.world;
                  agent := IMAGE (encode_sum o INR) d.agent;
                  env := s.env;
                  eval := s.eval |>) -: d.world
End

Definition is_subtensor_def:
  is_subtensor c d t ⇔
    t.world = (tensor c d).world ∧
    t.agent = (tensor c d).agent ∧
    t.env ⊆ (tensor c d).env ∧
    (∀a. t.eval a = restrict ((tensor c d).eval a) t.env) ∧
    c ≃ (mk_cf <| world := c.world;
                  agent := c.agent;
                  env := IMAGE encode_pair (d.agent × t.env);
                  eval := λa e.
                    t.eval (encode_pair (a, FST (decode_pair e)))
                           (SND (decode_pair e)) |>) -: c.world ∧
    d ≃ (mk_cf <| world := d.world;
                  agent := d.agent;
                  env := IMAGE encode_pair (c.agent × t.env);
                  eval := λa e.
                    t.eval (encode_pair (FST (decode_pair e), a))
                           (SND (decode_pair e)) |>) -: d.world
End

Theorem finite_subsum:
  finite_cf c ∧ finite_cf d ∧ is_subsum c d s ⇒ finite_cf s
Proof
  rw[is_subsum_def]
  \\ `finite_cf (sum c d)` by imp_res_tac finite_sum
  \\ fs[finite_cf_def]
  \\ metis_tac[SUBSET_FINITE]
QED

Theorem wf_subsum:
  wf c ∧ wf d ∧ is_subsum c d s ⇒ wf s
Proof
  strip_tac
  \\ `wf (sum c d)` by imp_res_tac wf_sum
  \\ fs[wf_def]
  \\ mp_tac finite_subsum \\ simp[] \\ strip_tac
  \\ fs[is_subsum_def]
  \\ simp[restrict_def]
  \\ gs[SUBSET_DEF]
  \\ rw[]
QED

Theorem finite_subtensor:
  finite_cf c ∧ finite_cf d ∧ is_subtensor c d s ⇒ finite_cf s
Proof
  rw[is_subtensor_def]
  \\ `finite_cf (tensor c d)` by imp_res_tac finite_tensor
  \\ fs[finite_cf_def]
  \\ metis_tac[SUBSET_FINITE]
QED

Theorem wf_subtensor:
  wf c ∧ wf d ∧ is_subtensor c d s ⇒ wf s
Proof
  strip_tac
  \\ `wf (tensor c d)` by imp_res_tac wf_tensor
  \\ fs[wf_def]
  \\ mp_tac finite_subtensor \\ simp[] \\ strip_tac
  \\ fs[is_subtensor_def]
  \\ simp[restrict_def]
  \\ gs[SUBSET_DEF]
  \\ rw[]
QED

Theorem subsum_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧ is_subsum c d s ⇒
  s ∈ chu_objects w
Proof
  rw[chu_objects_def]
  >- metis_tac[wf_subsum]
  \\ fs[is_subsum_def] \\ simp[sum_def]
QED

Theorem subtensor_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧ is_subtensor c d t ⇒
  t ∈ chu_objects w
Proof
  rw[chu_objects_def]
  >- metis_tac[wf_subtensor]
  \\ fs[is_subtensor_def] \\ simp[tensor_def]
QED

Definition comm_subsum_def:
  comm_subsum s = mk_cf
    <| world := s.world;
       agent := IMAGE comm_sum.map_agent s.agent;
       env := IMAGE comm_sum.map_env s.env;
       eval := λa e. s.eval (comm_sum.map_agent a) (comm_sum.map_env e) |>
End

Theorem comm_subsum_idem:
  wf s ∧
  s.agent ⊆ (sum c d).agent ∧
  s.env ⊆ (sum c d).env ⇒
  comm_subsum (comm_subsum s) = s
Proof
  rw[comm_subsum_def, mk_cf_def]
  \\ simp[cf_component_equality, PULL_EXISTS]
  \\ conj_tac
  >- (
    simp[EXTENSION, PULL_EXISTS]
    \\ fs[sum_def, comm_sum_def, PULL_EXISTS, SUBSET_DEF]
    \\ rw[EQ_IMP_THM] \\ res_tac \\ gs[]
    \\ qexists_tac`x` \\ simp[])
  \\ conj_tac
  >- (
    simp[EXTENSION, PULL_EXISTS]
    \\ simp[sum_def, comm_sum_def, PULL_EXISTS, UNCURRY]
    \\ fs[SUBSET_DEF, sum_def, PULL_EXISTS, EXISTS_PROD]
    \\ rw[EQ_IMP_THM] \\ res_tac \\ gs[]
    \\ qexists_tac`x` \\ simp[] )
  \\ simp[FUN_EQ_THM]
  \\ fs[SUBSET_DEF, sum_def, PULL_EXISTS, EXISTS_PROD, wf_def]
  \\ rw[comm_sum_def] \\ gvs[]
  \\ res_tac \\ gvs[UNCURRY]
  \\ TRY (
    first_x_assum irule
    \\ CCONTR_TAC \\ fs[] \\ fs[]
    \\ res_tac \\ fs[]
    \\ first_x_assum(qspecl_then[`a`,`e`]mp_tac)
    \\ simp[]
    \\ NO_TAC)
  \\ `F` suffices_by rw[]
  \\ qpat_x_assum`∀x y. _`mp_tac \\ simp[]
  \\ goal_assum(first_assum o mp_then Any mp_tac) \\ simp[]
  \\ goal_assum(first_assum o mp_then Any mp_tac) \\ simp[]
QED

Theorem comm_subsum_in_chu_objects:
  s ∈ chu_objects w ∧
  s.agent ⊆ (sum c d).agent ∧
  s.env ⊆ (sum c d).env
  ⇒ comm_subsum s ∈ chu_objects w
Proof
  rw[chu_objects_def, comm_subsum_def]
  \\ fs[wf_def, finite_cf_def]
  \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
  \\ rw[]
  \\ fs[SUBSET_DEF, sum_def, comm_sum_def]
  \\ res_tac \\ gs[UNCURRY]
QED

Theorem comm_subsum_iso:
  s ∈ chu_objects w ∧
  s.agent ⊆ (sum c d).agent ∧
  s.env ⊆ (sum c d).env
  ⇒
  s ≅ comm_subsum s -: chu w
Proof
  rw[iso_objs_thm, chu_iso_bij]
  \\ qexists_tac`mk_chu_morphism s (comm_subsum s) comm_sum`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ conj_tac >- metis_tac[comm_subsum_in_chu_objects]
    \\ simp[is_chu_morphism_def,mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[comm_subsum_def, PULL_EXISTS, mk_cf_def]
    \\ fs[SUBSET_DEF, sum_def, PULL_EXISTS]
    \\ rw[]
    \\ res_tac \\ gs[comm_sum_def, UNCURRY] )
  \\ fs[maps_to_in_chu]
  \\ simp[mk_chu_morphism_def]
  \\ simp[comm_subsum_def]
  \\ simp[BIJ_IFF_INV, PULL_EXISTS]
  \\ qexistsl_tac[`comm_sum.map_agent`,`comm_sum.map_env`]
  \\ fs[SUBSET_DEF, sum_def, PULL_EXISTS]
  \\ rw[]
  \\ res_tac \\ gs[comm_sum_def, UNCURRY]
  \\ qexists_tac`x` \\ simp[]
QED

Theorem is_subsum_comm_subsum:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
  is_subsum c d s ⇒ is_subsum d c (comm_subsum s)
Proof
  simp[is_subsum_def]
  \\ strip_tac
  \\ conj_tac >- simp[sum_def, UNION_COMM,comm_subsum_def]
  \\ conj_asm1_tac
  >- (
    simp[sum_def, comm_subsum_def,
         comm_sum_def, GSYM IMAGE_COMPOSE]
    \\ simp[combinTheory.o_DEF, UNION_COMM])
  \\ conj_asm1_tac
  >- (
    fs[SUBSET_DEF, PULL_EXISTS, comm_subsum_def,
       comm_sum_def, UNCURRY]
    \\ fs[sum_def]
    \\ gen_tac \\ strip_tac \\ res_tac
    \\ simp[] )
  \\ conj_tac
  >- (
    fs[comm_subsum_def]
    \\ simp[FUN_EQ_THM, restrict_def, mk_cf_def]
    \\ fs[SUBSET_DEF]
    \\ rw[]
    \\ res_tac
    \\ fs[sum_def, mk_cf_def, comm_sum_def,
          sum_eval_def, UNCURRY]
    \\ gs[] \\ rw[] \\ gs[] )
  \\ qmatch_assum_abbrev_tac`c ≃ c1 -: _`
  \\ qmatch_assum_abbrev_tac`d ≃ d1 -: _`
  \\ qmatch_goalsub_abbrev_tac`c ≃ c2 -: _`
  \\ qmatch_goalsub_abbrev_tac`d ≃ d2 -: _`
  \\ `c2 = comm_subsum c1`
  by (
    simp[cf_component_equality]
    \\ simp[Abbr`c2`, Abbr`c1`]
    \\ simp[comm_subsum_def, mk_cf_def]
    \\ conj_tac
    >- simp[EXTENSION, comm_sum_def, PULL_EXISTS]
    \\ simp[FUN_EQ_THM, restrict_def]
    \\ rw[] \\ gs[comm_sum_def]
    \\ `F` suffices_by rw[]
    \\ qpat_x_assum`∀x. _`mp_tac
    \\ simp[PULL_EXISTS]
    \\ dsimp[sum_def, PULL_EXISTS]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[] )
  \\ `d2 = comm_subsum d1`
  by (
    simp[cf_component_equality]
    \\ simp[Abbr`d2`, Abbr`d1`]
    \\ simp[comm_subsum_def, mk_cf_def]
    \\ conj_tac
    >- simp[EXTENSION, comm_sum_def, PULL_EXISTS]
    \\ simp[FUN_EQ_THM, restrict_def]
    \\ rw[] \\ gs[comm_sum_def]
    \\ `F` suffices_by rw[]
    \\ qpat_x_assum`∀x. _`mp_tac
    \\ simp[PULL_EXISTS]
    \\ dsimp[sum_def, PULL_EXISTS]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[] )
  \\ `sum c d ∈ chu_objects w` by simp[]
  \\ `c1 ∈ chu_objects w`
  by (
    simp[in_chu_objects, Abbr`c1`]
    \\ pop_assum mp_tac
    \\ qpat_x_assum`c ∈ chu_objects _ `mp_tac
    \\ rewrite_tac[in_chu_objects, wf_def]
    \\ simp[finite_cf_def]
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ ntac 2 strip_tac
    \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, SUBSET_DEF]
    \\ rw[]
    \\ first_x_assum irule \\ simp[]
    \\ rewrite_tac[sum_def] \\ simp[] )
  \\ `d1 ∈ chu_objects w`
  by (
    simp[in_chu_objects, Abbr`d1`]
    \\ qpat_x_assum`(sum _ _) ∈ _`mp_tac
    \\ qpat_x_assum`d ∈ chu_objects _ `mp_tac
    \\ rewrite_tac[in_chu_objects, wf_def]
    \\ simp[finite_cf_def]
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ ntac 2 strip_tac
    \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, SUBSET_DEF]
    \\ rw[]
    \\ first_x_assum irule \\ simp[]
    \\ rewrite_tac[sum_def] \\ simp[] )
  \\ `c.world = w ∧ d.world = w` by rfs[in_chu_objects]
  \\ conj_tac \\ irule homotopy_equiv_trans
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ irule iso_homotopy_equiv
  \\ rw[]
  \\ irule comm_subsum_iso
  \\ rw[]
  \\ simp[Abbr`c1`, Abbr`d1`]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[sum_def]
QED

Theorem is_subsum_comm:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ⇒
  BIJ comm_subsum (is_subsum c d) (is_subsum d c) ∧
    ∀s. is_subsum c d s ⇒ s ≅ (comm_subsum s) -: chu w
Proof
  reverse(rw[])
  >- (
    irule comm_subsum_iso
    \\ conj_tac >- metis_tac[subsum_in_chu_objects]
    \\ fs[is_subsum_def]
    \\ metis_tac[SUBSET_REFL] )
  \\ rw[BIJ_IFF_INV]
  >- (
    pop_assum mp_tac
    \\ simp[IN_DEF]
    \\ metis_tac[is_subsum_comm_subsum])
  \\ qexists_tac`comm_subsum`
  \\ conj_tac >- (
    simp[IN_DEF]
    \\ metis_tac[is_subsum_comm_subsum] )
  \\ rw[]
  \\ irule comm_subsum_idem
  \\ pop_assum mp_tac
  \\ simp[Once IN_DEF]
  \\ strip_tac
  \\ `x ∈ chu_objects w` by imp_res_tac subsum_in_chu_objects
  \\ fs[in_chu_objects]
  \\ fs[is_subsum_def]
  \\ metis_tac[SUBSET_REFL]
QED

Theorem comm_tensor_env_in_tensor_env:
  m ∈ (tensor c d).env ∧ c.world = d.world ⇒
  comm_tensor_env d c m ∈ (tensor d c).env
Proof
  rw[tensor_def, hom_def, maps_to_in_chu]
  \\ rw[comm_tensor_env_def]
  \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
  \\ simp[PULL_EXISTS]
  \\ qexists_tac`x.dom.world`
  \\ qmatch_goalsub_abbrev_tac`encode_morphism m`
  \\ qexists_tac`m`
  \\ conj_asm1_tac >- ( fs[maps_to_in_chu] \\ metis_tac[] )
  \\ simp[Abbr`m`]
  \\ fs[maps_to_in_chu] \\ gs[]
  \\ simp[mk_chu_morphism_def]
  \\ fs[is_chu_morphism_def]
  \\ fs[restrict_def]
QED

Theorem comm_tensor_env_idem:
  (m ∈ chu w | c → swap d |) ⇒
  comm_tensor_env c d (comm_tensor_env d c (encode_morphism m))
  = encode_morphism m
Proof
  rw[comm_tensor_env_def]
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
  \\ fs[hom_def]
  \\ conj_asm1_tac
  >- (
    fs[maps_to_in_chu]
    \\ fs[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def] )
  \\ AP_TERM_TAC
  \\ simp[morphism_component_equality]
  \\ fs[maps_to_in_chu]
  \\ simp[chu_morphism_map_component_equality,
          mk_chu_morphism_def]
  \\ fs[is_chu_morphism_def]
  \\ fs[restrict_def, extensional_def, FUN_EQ_THM]
  \\ rw[]
QED

Definition comm_subtensor_def:
  comm_subtensor c d t = mk_cf
    <| world := t.world;
       agent := IMAGE comm_sum.map_env t.agent;
       env := IMAGE (comm_tensor_env c d) t.env;
       eval := λa e. t.eval (comm_sum.map_env a) (comm_tensor_env d c e) |>
End

Theorem comm_subtensor_idem:
  wf t ∧
  t.agent ⊆ (tensor c d).agent ∧
  t.env ⊆ (tensor c d).env ⇒
  comm_subtensor c d (comm_subtensor d c t) = t
Proof
  rw[comm_subtensor_def, mk_cf_def]
  \\ simp[cf_component_equality, PULL_EXISTS]
  \\ conj_tac
  >- (
    simp[EXTENSION, PULL_EXISTS]
    \\ simp[sum_def, comm_sum_def, PULL_EXISTS, UNCURRY]
    \\ fs[SUBSET_DEF, tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ rw[EQ_IMP_THM] \\ res_tac \\ gs[]
    \\ qexists_tac`x` \\ simp[] )
  \\ conj_tac
  >- (
    simp[EXTENSION, PULL_EXISTS]
    \\ fs[tensor_def, SUBSET_DEF]
    \\ rw[EQ_IMP_THM] \\ res_tac \\ gs[]
    \\ TRY (qexists_tac`x` \\ simp[])
    \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
    \\ fs[hom_def] \\ metis_tac[] )
  \\ simp[FUN_EQ_THM]
  \\ fs[SUBSET_DEF, tensor_def, PULL_EXISTS, EXISTS_PROD, wf_def]
  \\ rw[comm_sum_def] \\ gvs[]
  \\ res_tac \\ gvs[UNCURRY]
  \\ TRY (
    qpat_x_assum`_ = _`mp_tac
    \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
    \\ conj_tac >- metis_tac[]
    \\ disch_then(mp_tac o Q.AP_TERM`comm_tensor_env c d`)
    \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
    \\ conj_tac >- metis_tac[]
    \\ rw[] )
  \\ TRY (
    first_x_assum irule
    \\ CCONTR_TAC \\ fs[] \\ fs[]
    \\ res_tac \\ fs[]
    \\ first_x_assum(qspecl_then[`a`,`e`]mp_tac)
    \\ simp[]
    \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
    \\ metis_tac[])
  \\ `F` suffices_by rw[]
  \\ qpat_x_assum`∀x y. _`mp_tac \\ simp[]
  \\ goal_assum(first_assum o mp_then Any mp_tac) \\ simp[]
  \\ goal_assum(first_assum o mp_then Any mp_tac) \\ simp[]
  \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
  \\ metis_tac[]
QED

Theorem comm_subtensor_in_chu_objects:
  s ∈ chu_objects w ∧
  s.agent ⊆ (tensor c d).agent ∧
  s.env ⊆ (tensor c d).env
  ⇒ comm_subtensor d c s ∈ chu_objects w
Proof
  rw[chu_objects_def, comm_subtensor_def]
  \\ fs[wf_def, finite_cf_def]
  \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
  \\ rw[]
  \\ fs[SUBSET_DEF, tensor_def, comm_sum_def]
  \\ res_tac \\ gs[UNCURRY]
  \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
  \\ metis_tac[]
QED

Theorem comm_subtensor_iso:
  s ∈ chu_objects w ∧
  s.agent ⊆ (tensor c d).agent ∧
  s.env ⊆ (tensor c d).env
  ⇒
  s ≅ comm_subtensor d c s -: chu w
Proof
  rw[iso_objs_thm, chu_iso_bij]
  \\ qexists_tac`mk_chu_morphism s (comm_subtensor d c s)
      <| map_agent := comm_sum.map_env;
         map_env := comm_tensor_env c d |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ conj_tac >- metis_tac[comm_subtensor_in_chu_objects]
    \\ simp[is_chu_morphism_def,mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[comm_subtensor_def, PULL_EXISTS, mk_cf_def]
    \\ fs[SUBSET_DEF, tensor_def, PULL_EXISTS]
    \\ rw[]
    \\ res_tac \\ gs[comm_sum_def, UNCURRY]
    \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
    >- metis_tac[]
    \\ conj_tac >- metis_tac[]
    \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ simp[PAIR_FST_SND_EQ])
  \\ fs[maps_to_in_chu]
  \\ simp[mk_chu_morphism_def]
  \\ simp[comm_subtensor_def]
  \\ simp[BIJ_IFF_INV, PULL_EXISTS]
  \\ qexistsl_tac[`comm_sum.map_env`,`comm_tensor_env d c`]
  \\ fs[SUBSET_DEF, tensor_def, PULL_EXISTS]
  \\ rw[]
  \\ res_tac \\ gs[comm_sum_def, UNCURRY]
  \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
  \\ simp[]
  \\ TRY(qexists_tac`x` \\ simp[] \\ NO_TAC)
  \\ metis_tac[]
QED

Theorem is_subtensor_comm_subtensor:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
  is_subtensor c d s ⇒ is_subtensor d c (comm_subtensor d c s)
Proof
  simp[is_subtensor_def]
  \\ strip_tac
  \\ conj_tac >- simp[tensor_def, UNION_COMM,comm_subtensor_def]
  \\ conj_asm1_tac
  >- (
    simp[tensor_def, comm_subtensor_def,
         comm_sum_def, EXTENSION, PULL_EXISTS, EXISTS_PROD]
    \\ metis_tac[] )
  \\ conj_asm1_tac
  >- (
    fs[SUBSET_DEF, PULL_EXISTS, comm_subtensor_def]
    \\ rw[]
    \\ irule comm_tensor_env_in_tensor_env
    \\ fs[in_chu_objects])
  \\ conj_tac
  >- (
    fs[comm_subtensor_def]
    \\ simp[FUN_EQ_THM, restrict_def, mk_cf_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ rpt gen_tac
    \\ reverse IF_CASES_TAC
    >- (
      IF_CASES_TAC \\ simp[] \\ fs[]
      \\ `tensor d c ∈ chu_objects w` by simp[]
      \\ pop_assum mp_tac
      \\ rewrite_tac[chu_objects_def, wf_def]
      \\ simp[] \\ strip_tac
      \\ first_x_assum irule
      \\ metis_tac[] )
    \\ fs[]
    \\ res_tac
    \\ pop_assum mp_tac
    \\ simp_tac(srw_ss())[Once tensor_def]
    \\ strip_tac \\ gvs[]
    \\ DEP_REWRITE_TAC[comm_tensor_env_idem]
    \\ conj_tac >- rfs[in_chu_objects]
    \\ simp[]
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ pop_assum mp_tac \\ simp[hom_def]
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ qmatch_goalsub_abbrev_tac`_.eval _ m`
    \\ `c.world = w ∧ d.world = w` by rfs[in_chu_objects]
    \\ `comm_tensor_env d c m ∈ (tensor d c).env` by metis_tac[]
    \\ pop_assum mp_tac
    \\ simp_tac(srw_ss())[tensor_def, EXISTS_PROD]
    \\ simp[hom_def]
    \\ ntac 3 strip_tac
    \\ simp[mk_cf_def, EXISTS_PROD, comm_sum_def, Abbr`m`]
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ fs[]
    \\ qpat_x_assum`_ = encode_morphism _`mp_tac
    \\ simp[comm_tensor_env_def]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ fs[]
    \\ disch_then(mp_tac o Q.AP_TERM`decode_morphism d (swap c)`)
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ conj_tac
    >- (
      fs[maps_to_in_chu]
      \\ fs[is_chu_morphism_def, mk_chu_morphism_def]
      \\ fs[restrict_def] )
    \\ strip_tac
    \\ gvs[]
    \\ simp[mk_chu_morphism_def, restrict_def]
    \\ fs[maps_to_in_chu, is_chu_morphism_def] )
  \\ qmatch_assum_abbrev_tac`c ≃ c1 -: _`
  \\ qmatch_assum_abbrev_tac`d ≃ d1 -: _`
  \\ qmatch_goalsub_abbrev_tac`c ≃ c2 -: _`
  \\ qmatch_goalsub_abbrev_tac`d ≃ d2 -: _`
  \\ `c.world = w ∧ d.world = w` by rfs[in_chu_objects]
  \\ `tensor c d ∈ chu_objects w` by simp[]
  \\ `c1 ∈ chu_objects w`
  by (
    pop_assum mp_tac
    \\ simp_tac(srw_ss())[in_chu_objects, Abbr`c1`]
    \\ simp[wf_def]
    \\ strip_tac
    \\ qpat_x_assum`c ∈ chu_objects _`mp_tac
    \\ qpat_x_assum`d ∈ chu_objects _`mp_tac
    \\ simp[in_chu_objects, wf_def]
    \\ fs[finite_cf_def]
    \\ ntac 2 strip_tac
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, SUBSET_DEF]
    \\ rw[]
    \\ first_x_assum irule \\ simp[]
    \\ rewrite_tac[tensor_def] \\ simp[] )
  \\ `d1 ∈ chu_objects w`
  by (
    qpat_x_assum`tensor _ _ ∈ _` mp_tac
    \\ simp_tac(srw_ss())[in_chu_objects, Abbr`d1`]
    \\ simp[wf_def]
    \\ strip_tac
    \\ qpat_x_assum`c ∈ chu_objects _`mp_tac
    \\ qpat_x_assum`d ∈ chu_objects _`mp_tac
    \\ simp[in_chu_objects, wf_def]
    \\ fs[finite_cf_def]
    \\ ntac 2 strip_tac
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, SUBSET_DEF]
    \\ rw[]
    \\ first_x_assum irule \\ simp[]
    \\ rewrite_tac[tensor_def] \\ simp[] )
  \\ `c2 ∈ chu_objects w`
  by (
    qpat_x_assum`c1 ∈ chu_objects _`mp_tac
    \\ simp[in_chu_objects, Abbr`c1`, Abbr`c2`]
    \\ simp[finite_cf_def]
    \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ simp[comm_subtensor_def, mk_cf_def, PULL_EXISTS]
    \\ simp[restrict_def, comm_sum_def]
    \\ disch_then assume_tac
    \\ reverse conj_tac
    >- metis_tac[IMAGE_FINITE]
    \\ pop_assum kall_tac
    \\ simp[FORALL_PROD, UNCURRY, PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ `x ∈ (tensor c d).env` by fs[SUBSET_DEF]
    \\ pop_assum mp_tac
    \\ simp[Once tensor_def]
    \\ strip_tac \\ simp[]
    \\ DEP_REWRITE_TAC[comm_tensor_env_idem]
    \\ gs[]
    \\ `tensor c d ∈ chu_objects w` by simp[]
    \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [in_chu_objects, wf_def]
    \\ strip_tac \\ fs[]
    \\ first_x_assum irule
    \\ simp[tensor_def] )
  \\ `d2 ∈ chu_objects w`
  by (
    qpat_x_assum`d1 ∈ chu_objects _`mp_tac
    \\ simp[in_chu_objects, Abbr`d1`, Abbr`d2`]
    \\ simp[finite_cf_def]
    \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ simp[comm_subtensor_def, mk_cf_def, PULL_EXISTS]
    \\ simp[restrict_def, comm_sum_def]
    \\ disch_then assume_tac
    \\ reverse conj_tac
    >- metis_tac[IMAGE_FINITE]
    \\ pop_assum kall_tac
    \\ simp[FORALL_PROD, UNCURRY, PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ `x ∈ (tensor c d).env` by fs[SUBSET_DEF]
    \\ pop_assum mp_tac
    \\ simp[Once tensor_def]
    \\ strip_tac \\ simp[]
    \\ DEP_REWRITE_TAC[comm_tensor_env_idem]
    \\ gs[]
    \\ `tensor c d ∈ chu_objects w` by simp[]
    \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [in_chu_objects, wf_def]
    \\ strip_tac \\ fs[]
    \\ first_x_assum irule
    \\ simp[tensor_def] )
  \\ `c1 ≃ c2 -: w`
  by (
    simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism c1 c2 <| map_agent := I;
         map_env := λp. encode_pair (FST (decode_pair p),
           comm_tensor_env c d (SND (decode_pair p))) |>`
    \\ qexists_tac`mk_chu_morphism c2 c1 <| map_agent := I;
         map_env := λp. encode_pair (FST (decode_pair p),
           comm_tensor_env d c (SND (decode_pair p))) |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c1`, Abbr`c2`, PULL_EXISTS, EXISTS_PROD]
      \\ simp[mk_cf_def, restrict_def]
      \\ simp[comm_subtensor_def, PULL_EXISTS]
      \\ conj_asm1_tac
      >- (
        rw[]
        \\ `x ∈ (tensor c d).env` by fs[SUBSET_DEF]
        \\ fs[Once tensor_def]
        \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
        \\ fs[] \\ metis_tac[] )
      \\ rpt gen_tac \\ strip_tac
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ simp[mk_cf_def, PULL_EXISTS, restrict_def, comm_sum_def]
      \\ rw[]
      \\ `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ metis_tac[] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c1`, Abbr`c2`, PULL_EXISTS, EXISTS_PROD]
      \\ simp[mk_cf_def, restrict_def]
      \\ simp[comm_subtensor_def, PULL_EXISTS]
      \\ rpt gen_tac \\ strip_tac
      \\ simp[mk_cf_def, PULL_EXISTS, restrict_def, comm_sum_def]
      \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ fs[SUBSET_DEF] \\ res_tac
      \\ pop_assum mp_tac
      \\ simp_tac(srw_ss())[Once tensor_def]
      \\ strip_tac \\ simp[]
      \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
      \\ fs[]
      \\ metis_tac[] )
    \\ imp_res_tac compose_in_chu
    \\ simp[homotopic_id_map_agent_id]
    \\ simp[restrict_def, mk_chu_morphism_def]
    \\ simp[Abbr`c1`, Abbr`c2`] )
  \\ `d1 ≃ d2 -: w`
  by (
    simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism d1 d2 <| map_agent := I;
         map_env := λp. encode_pair (FST (decode_pair p),
           comm_tensor_env c d (SND (decode_pair p))) |>`
    \\ qexists_tac`mk_chu_morphism d2 d1 <| map_agent := I;
         map_env := λp. encode_pair (FST (decode_pair p),
           comm_tensor_env d c (SND (decode_pair p))) |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`d1`, Abbr`d2`, PULL_EXISTS, EXISTS_PROD]
      \\ simp[mk_cf_def, restrict_def]
      \\ simp[comm_subtensor_def, PULL_EXISTS]
      \\ conj_asm1_tac
      >- (
        rw[]
        \\ `x ∈ (tensor c d).env` by fs[SUBSET_DEF]
        \\ fs[Once tensor_def]
        \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
        \\ fs[] \\ metis_tac[] )
      \\ rpt gen_tac \\ strip_tac
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ simp[mk_cf_def, PULL_EXISTS, restrict_def, comm_sum_def]
      \\ rw[]
      \\ `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ metis_tac[] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`d1`, Abbr`d2`, PULL_EXISTS, EXISTS_PROD]
      \\ simp[mk_cf_def, restrict_def]
      \\ simp[comm_subtensor_def, PULL_EXISTS]
      \\ rpt gen_tac \\ strip_tac
      \\ simp[mk_cf_def, PULL_EXISTS, restrict_def, comm_sum_def]
      \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ fs[SUBSET_DEF] \\ res_tac
      \\ pop_assum mp_tac
      \\ simp_tac(srw_ss())[Once tensor_def]
      \\ strip_tac \\ simp[]
      \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
      \\ fs[]
      \\ metis_tac[] )
    \\ imp_res_tac compose_in_chu
    \\ simp[homotopic_id_map_agent_id]
    \\ simp[mk_chu_morphism_def, restrict_def]
    \\ simp[Abbr`d1`, Abbr`d2`] )
  \\ metis_tac[homotopy_equiv_trans]
QED

Theorem is_subtensor_comm:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ⇒
  BIJ (comm_subtensor d c) (is_subtensor c d) (is_subtensor d c) ∧
  ∀t. is_subtensor c d t ⇒ t ≅ comm_subtensor d c t -: chu w
Proof
  reverse(rw[])
  >- (
    irule comm_subtensor_iso
    \\ conj_tac >- metis_tac[subtensor_in_chu_objects]
    \\ fs[is_subtensor_def])
  \\ rw[BIJ_IFF_INV]
  >- (
    pop_assum mp_tac
    \\ simp[IN_DEF]
    \\ metis_tac[is_subtensor_comm_subtensor])
  \\ qexists_tac`comm_subtensor c d`
  \\ conj_tac >- (
    simp[IN_DEF]
    \\ metis_tac[is_subtensor_comm_subtensor] )
  \\ rw[]
  \\ irule comm_subtensor_idem
  \\ pop_assum mp_tac
  \\ simp[Once IN_DEF]
  \\ strip_tac
  \\ `x ∈ chu_objects w` by imp_res_tac subtensor_in_chu_objects
  \\ fs[chu_objects_def]
  \\ fs[is_subtensor_def]
QED

Theorem sum_is_subsum:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
  c.env ≠ ∅ ∧ d.env ≠ ∅
  ⇒
  is_subsum c d (sum c d)
Proof
  simp[is_subsum_def, restrict_def]
  \\ strip_tac
  \\ conj_tac
  >- (
    `sum c d ∈ chu_objects w` by simp[]
    \\ fs[in_chu_objects]
    \\ fs[wf_def, FUN_EQ_THM] \\ rw[] )
  \\ qmatch_goalsub_abbrev_tac`c ≃ c' -: _`
  \\ qmatch_goalsub_abbrev_tac`d ≃ d' -: _`
  \\ `is_chu_morphism c c' (mk_chu_morphism c c'
        <| map_agent := encode_sum o INL;
           map_env := FST o decode_pair |>).map`
  by (
    simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`c'`, mk_cf_def]
    \\ simp[sum_def, PULL_EXISTS, FORALL_PROD, mk_cf_def]
    \\ simp[sum_eval_def])
  \\ `is_chu_morphism d d' (mk_chu_morphism d d'
        <| map_agent := encode_sum o INR;
           map_env := SND o decode_pair |>).map`
  by (
    simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d'`, mk_cf_def]
    \\ simp[sum_def, PULL_EXISTS, FORALL_PROD, mk_cf_def]
    \\ simp[sum_eval_def])
  \\ qmatch_assum_abbrev_tac`is_chu_morphism c c' f.map`
  \\ qmatch_assum_abbrev_tac`is_chu_morphism d d' g.map`
  \\ `c' ∈ chu_objects w ∧ d' ∈ chu_objects w`
  by (
    simp[Abbr`c'`, Abbr`d'`]
    \\ `sum c d ∈ chu_objects w` by simp[]
    \\ fs[in_chu_objects]
    \\ fs[wf_def, finite_cf_def]
    \\ fs[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ fs[sum_def] )
  \\ `f :- c → c' -: chu w ∧ g :- d → d' -: chu w`
  by ( simp[maps_to_in_chu] \\ simp[Abbr`f`, Abbr`g`] )
  \\ `is_chu_morphism c' c (mk_chu_morphism c' c
        <| map_agent := OUTL o decode_sum;
           map_env := λe. encode_pair (e, CHOICE d.env) |>).map`
  by (
    simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`c'`, mk_cf_def]
    \\ simp[sum_def, PULL_EXISTS, FORALL_PROD, mk_cf_def]
    \\ simp[CHOICE_DEF]
    \\ simp[sum_eval_def])
  \\ `is_chu_morphism d' d (mk_chu_morphism d' d
        <| map_agent := OUTR o decode_sum;
           map_env := λe. encode_pair (CHOICE c.env, e) |>).map`
  by (
    simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d'`, mk_cf_def]
    \\ simp[sum_def, PULL_EXISTS, FORALL_PROD, mk_cf_def]
    \\ simp[CHOICE_DEF]
    \\ simp[sum_eval_def])
  \\ qmatch_assum_abbrev_tac`is_chu_morphism c' c f'.map`
  \\ qmatch_assum_abbrev_tac`is_chu_morphism d' d g'.map`
  \\ `f' :- c' → c -: chu w ∧ g' :- d' → d -: chu w`
  by ( simp[maps_to_in_chu] \\ simp[Abbr`f'`, Abbr`g'`] )
  \\ `homotopic w (f' o f -: chu w) (id c -: chu w)`
  by (
    imp_res_tac compose_in_chu
    \\ simp[homotopic_id_map_agent_id]
    \\ simp[Abbr`f`, Abbr`f'`, mk_chu_morphism_def]
    \\ simp[restrict_def, FUN_EQ_THM]
    \\ simp[Abbr`c'`] )
  \\ `homotopic w (g' o g -: chu w) (id d -: chu w)`
  by (
    imp_res_tac compose_in_chu
    \\ simp[homotopic_id_map_agent_id]
    \\ simp[Abbr`g`, Abbr`g'`, mk_chu_morphism_def]
    \\ simp[restrict_def, FUN_EQ_THM]
    \\ simp[Abbr`d'`] )
  \\ `homotopic w (f o f' -: chu w) (id c' -: chu w)`
  by (
    imp_res_tac compose_in_chu
    \\ simp[homotopic_id_map_agent_id]
    \\ simp[Abbr`f`, Abbr`f'`, mk_chu_morphism_def]
    \\ simp[restrict_def, FUN_EQ_THM]
    \\ simp[Abbr`c'`, PULL_EXISTS])
  \\ `homotopic w (g o g' -: chu w) (id d' -: chu w)`
  by (
    imp_res_tac compose_in_chu
    \\ simp[homotopic_id_map_agent_id]
    \\ simp[Abbr`g`, Abbr`g'`, mk_chu_morphism_def]
    \\ simp[restrict_def, FUN_EQ_THM]
    \\ simp[Abbr`d'`, PULL_EXISTS])
  \\ simp[homotopy_equiv_def]
  \\ fs[in_chu_objects]
  \\ metis_tac[]
QED

Theorem subsum_subagent:
  c1 ∈ chu_objects w ∧
  c2 ∈ chu_objects w ∧
  is_subsum c1 c2 d ⇒
  c1 ◁ d -: w ∧ c2 ◁ d -: w
Proof
  qho_match_abbrev_tac`P c1 c2 d ⇒ Q c1 c2 d`
  \\ `∀c1 c2 d. P c1 c2 d ⇒ Q c1 c1 d`
  suffices_by (
    simp[Abbr`P`, Abbr`Q`]
    \\ ntac 2 strip_tac
    \\ conj_tac >- metis_tac[]
    \\ `is_subsum c2 c1 (comm_subsum d)`
    by metis_tac[is_subsum_comm_subsum]
    \\ irule subagent_homotopy_equiv
    \\ qexistsl_tac[`c2`,`comm_subsum d`]
    \\ simp[]
    \\ conj_tac
    >- (
      simp[Once homotopy_equiv_sym]
      \\ irule iso_homotopy_equiv
      \\ metis_tac[is_subsum_comm] )
    \\ metis_tac[] )
  \\ simp[Abbr`P`, Abbr`Q`]
  \\ rpt gen_tac \\ strip_tac
  \\ `d ∈ chu_objects w` by metis_tac[subsum_in_chu_objects]
  \\ simp[subagent_currying]
  \\ simp[currying_subagent_def]
  \\ `c1.world = w ∧ c2.world = w` by rfs[in_chu_objects]
  \\ gs[is_subsum_def]
  \\ qmatch_assum_abbrev_tac`c1 ≃ b1 -: _`
  \\ qexists_tac`mk_cf <| world := d.agent; agent := b1.agent;
       env := {""}; eval := K |>`
  \\ qmatch_goalsub_abbrev_tac`c1 ≃ move d b2 -: _`
  \\ `b1 ∈ chu_objects w`
  by (
    qpat_x_assum`d ∈ _`mp_tac
    \\ fs[in_chu_objects, Abbr`b1`]
    \\ fs[wf_def, finite_cf_def]
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ `(sum c1 c2).world = w` by simp[sum_def]
    \\ rw[]
    \\ first_x_assum irule
    \\ simp[Once sum_def] )
  \\ `b2 ∈ chu_objects d.agent`
  by (
    simp[in_chu_objects, Abbr`b2`]
    \\ simp[SUBSET_DEF, image_def]
    \\ conj_tac >- (
      simp[Abbr`b1`, PULL_EXISTS] \\ simp[sum_def] )
    \\ simp[finite_cf_def, Abbr`b1`]
    \\ `wf c1 ∧ wf (sum c1 c2)` by rfs[in_chu_objects]
    \\ `finite_cf c1 ∧ finite_cf (sum c1 c2)` by fs[wf_def]
    \\ fs[finite_cf_def] )
  \\ `move d b2 ∈ chu_objects w`
  by ( irule move_in_chu_objects \\ simp[] )
  \\ `b1 ≃ move d b2 -: w`
  suffices_by metis_tac[homotopy_equiv_trans]
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism b1 (move d b2) <| map_agent := I;
       map_env := SND o decode_pair |>`
  \\ qexists_tac`mk_chu_morphism (move d b2) b1 <| map_agent := I;
       map_env := λe. encode_pair ("", e) |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def, PULL_EXISTS]
    \\ simp[restrict_def]
    \\ simp[Abbr`b2`, move_def, Abbr`b1`, PULL_EXISTS]
    \\ simp[mk_cf_def, restrict_def] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def, PULL_EXISTS]
    \\ simp[restrict_def]
    \\ simp[Abbr`b2`, move_def, Abbr`b1`, PULL_EXISTS]
    \\ simp[mk_cf_def, restrict_def] )
  \\ imp_res_tac compose_in_chu
  \\ simp[homotopic_id_map_agent_id]
  \\ simp[Abbr`b1`, Abbr`b2`, mk_chu_morphism_def, restrict_def, FUN_EQ_THM]
QED

Theorem subtensor_subagent:
  c1 ∈ chu_objects w ∧
  c2 ∈ chu_objects w ∧
  is_subtensor c1 c2 d ⇒
  c1 ◁ d -: w ∧ c2 ◁ d -: w
Proof
  qho_match_abbrev_tac`P c1 c2 d ⇒ Q c1 c2 d`
  \\ `∀c1 c2 d. P c1 c2 d ⇒ Q c1 c1 d`
  suffices_by (
    simp[Abbr`P`, Abbr`Q`]
    \\ ntac 2 strip_tac
    \\ conj_tac >- metis_tac[]
    \\ `is_subtensor c2 c1 (comm_subtensor c2 c1 d)`
    by metis_tac[is_subtensor_comm_subtensor]
    \\ irule subagent_homotopy_equiv
    \\ qexistsl_tac[`c2`,`comm_subtensor c2 c1 d`]
    \\ simp[]
    \\ conj_tac
    >- (
      simp[Once homotopy_equiv_sym]
      \\ irule iso_homotopy_equiv
      \\ metis_tac[is_subtensor_comm] )
    \\ metis_tac[] )
  \\ simp[Abbr`P`, Abbr`Q`]
  \\ rpt gen_tac \\ strip_tac
  \\ `d ∈ chu_objects w` by metis_tac[subtensor_in_chu_objects]
  \\ simp[subagent_currying]
  \\ simp[currying_subagent_def]
  \\ `c1.world = w ∧ c2.world = w` by rfs[in_chu_objects]
  \\ gs[is_subtensor_def]
  \\ qmatch_assum_abbrev_tac`c1 ≃ b1 -: _`
  \\ qexists_tac`mk_cf <| world := d.agent; agent := c1.agent;
       env := c2.agent; eval := CURRY encode_pair |>`
  \\ qmatch_goalsub_abbrev_tac`c1 ≃ move d b2 -: _`
  \\ `b1 ∈ chu_objects w`
  by (
    qpat_x_assum`d ∈ _`mp_tac
    \\ fs[in_chu_objects, Abbr`b1`]
    \\ fs[wf_def, finite_cf_def]
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ `(tensor c1 c2).world = w` by simp[tensor_def]
    \\ rw[]
    \\ first_x_assum irule
    \\ simp[Once tensor_def] )
  \\ conj_asm1_tac >- (
    simp[in_chu_objects, Abbr`b2`]
    \\ simp[SUBSET_DEF, image_def, PULL_EXISTS]
    \\ conj_tac >- simp[tensor_def]
    \\ simp[finite_cf_def]
    \\ `wf c1 ∧ wf c2 ∧ wf (tensor c1 c2)` by rfs[in_chu_objects]
    \\ `finite_cf c1 ∧ finite_cf c2 ∧ finite_cf (tensor c1 c2)` by fs[wf_def]
    \\ fs[finite_cf_def] )
  \\ `move d b2 ∈ chu_objects w`
  by ( irule move_in_chu_objects \\ simp[] )
  \\ `b1 = move d b2`
  suffices_by metis_tac[homotopy_equiv_trans, homotopy_equiv_refl]
  \\ simp[cf_component_equality]
  \\ simp[Abbr`b1`, Abbr`b2`]
  \\ simp[Once tensor_def]
  \\ simp[move_def, mk_cf_def]
  \\ simp[FUN_EQ_THM]
  \\ simp[restrict_def]
  \\ rpt gen_tac
  \\ reverse IF_CASES_TAC \\ simp[]
  \\ reverse IF_CASES_TAC \\ simp[]
  \\ fs[]
QED

Theorem subsum_homotopy_equiv:
  c1 ∈ chu_objects w ∧
  c2 ∈ chu_objects w ∧
  is_subsum c1 c2 d ∧
  c1' ≃ c1 -: w ∧
  c2' ≃ c2 -: w
  ⇒
  ∃d'. d' ≃ d -: w ∧
    is_subsum c1' c2' d'
Proof
  strip_tac
  \\ `d ∈ chu_objects w` by metis_tac[subsum_in_chu_objects]
  \\ qpat_x_assum`is_subsum _ _ _`mp_tac
  \\ simp[Once is_subsum_def] \\ strip_tac
  \\ qmatch_assum_abbrev_tac`c1 ≃ b1 -: _`
  \\ qmatch_assum_abbrev_tac`c2 ≃ b2 -: _`
  \\ qpat_x_assum`c1' ≃ _ -: _`mp_tac
  \\ qpat_x_assum`c2' ≃ _ -: _`mp_tac
  \\ simp[Once homotopy_equiv_def]
  \\ disch_then(qx_choosel_then[`f2`,`g2`]strip_assume_tac)
  \\ simp[Once homotopy_equiv_def]
  \\ disch_then(qx_choosel_then[`f1`,`g1`]strip_assume_tac)
  \\ qabbrev_tac`f = (pair$## f1.map.map_env f2.map.map_env)`
  \\ qexists_tac`mk_cf <|
       world := w;
       agent := (sum c1' c2').agent;
       env := IMAGE (encode_pair o f o decode_pair) d.env;
       eval := sum_eval c1'.eval c2'.eval |>`
  \\ qmatch_goalsub_abbrev_tac`d' ≃ d -: _`
  \\ `c1' ∈ chu_objects w ∧ c2' ∈ chu_objects w` by fs[maps_to_in_chu]
  \\ `c1.world = w ∧ c2.world = w ∧ d.world = w ∧
      c1'.world = w ∧ c2'.world = w` by fs[in_chu_objects]
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ `d' ∈ chu_objects w`
  by (
    simp[in_chu_objects, Abbr`d'`]
    \\ `sum c1' c2' ∈ chu_objects w` by simp[] \\ pop_assum mp_tac
    \\ `sum c1 c2 ∈ chu_objects w` by simp[] \\ pop_assum mp_tac
    \\ rewrite_tac[in_chu_objects]
    \\ rewrite_tac[wf_def, finite_cf_def]
    \\ simp[]
    \\ ntac 2 strip_tac
    \\ reverse conj_tac >- metis_tac[IMAGE_FINITE, SUBSET_FINITE]
    \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ rpt strip_tac
    \\ qmatch_goalsub_abbrev_tac`q a b ∈ w`
    \\ `q a b = (sum c1' c2').eval a b ∧ b ∈ (sum c1' c2').env` suffices_by  metis_tac[]
    \\ simp[Abbr`q`, sum_def, mk_cf_def, EXISTS_PROD, Abbr`b`]
    \\ qpat_x_assum`d.env ⊆ _`mp_tac
    \\ simp[SUBSET_DEF]
    \\ disch_then drule
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ simp[sum_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Abbr`f`]
    \\ metis_tac[maps_to_in_chu, is_chu_morphism_def])
  \\ simp[homotopy_equiv_def, PULL_EXISTS]
  \\ qexists_tac`mk_chu_morphism d' d <|
       map_agent := λa. sum_CASE (decode_sum a) (encode_sum o INL o f1.map.map_agent) (encode_sum o INR o f2.map.map_agent);
       map_env := encode_pair o f o decode_pair |>`
  \\ `SURJ (encode_pair o f o decode_pair) d.env d'.env`
  by (
    simp[SURJ_DEF, Abbr`f`, FORALL_PROD, EXISTS_PROD]
    \\ simp[Abbr`d'`, PULL_EXISTS]
    \\ metis_tac[] )
  \\ qmatch_assum_abbrev_tac`SURJ ff _ _`
  \\ qexists_tac`mk_chu_morphism d d' <|
       map_agent := λa. sum_CASE (decode_sum a) (encode_sum o INL o g1.map.map_agent) (encode_sum o INR o g2.map.map_agent);
       map_env := λe'. @e. e ∈ d.env ∧ e' = ff e
       |>`
  \\ qmatch_goalsub_abbrev_tac`homotopic _ (j o k -: _)`
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`k`, Abbr`ff`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d'`]
    \\ conj_tac >- metis_tac[]
    \\ conj_tac
    >- (
      simp[sum_def, PULL_EXISTS]
      \\ fs[maps_to_in_chu, is_chu_morphism_def]
      \\ rw[] \\ simp[] )
    \\ simp[mk_cf_def]
    \\ rpt gen_tac
    \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ simp[sum_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD]
    \\ qpat_x_assum`d.env ⊆ _`mp_tac
    \\ simp[SUBSET_DEF]
    \\ disch_then drule
    \\ simp[sum_def, EXISTS_PROD]
    \\ strip_tac \\ simp[]
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ simp[sum_def, PULL_EXISTS]
    \\ strip_tac \\ simp[sum_eval_def]
    \\ fs[maps_to_in_chu, is_chu_morphism_def, Abbr`f`] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`j`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ fs[Abbr`d'`, PULL_EXISTS]
    \\ conj_tac >- metis_tac[]
    \\ conj_tac
    >- (
      simp_tac(srw_ss())[sum_def, PULL_EXISTS]
      \\ fs[maps_to_in_chu, is_chu_morphism_def]
      \\ rw[] \\ simp[] )
    \\ simp[mk_cf_def]
    \\ rpt gen_tac
    \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac \\ simp[]
      \\ qpat_x_assum`a ∈ _`mp_tac
      \\ simp_tac(srw_ss())[sum_def, PULL_EXISTS]
      \\ strip_tac \\ simp[]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ pop_assum kall_tac
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ qx_gen_tac`y`
    \\ strip_tac \\ simp[]
    \\ simp_tac(srw_ss())[sum_def]
    \\ simp[mk_cf_def, PULL_EXISTS, EXISTS_PROD]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac \\ simp[] \\ fs[]
      \\ qpat_x_assum`a ∈ _`mp_tac
      \\ simp_tac(srw_ss())[sum_def, PULL_EXISTS]
      \\ qpat_x_assum`d.env ⊆ _`mp_tac
      \\ simp[SUBSET_DEF]
      \\ simp_tac(srw_ss())[sum_def, PULL_EXISTS, EXISTS_PROD]
      \\ metis_tac[])
    \\ pop_assum kall_tac
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ simp_tac(srw_ss())[sum_def, PULL_EXISTS]
    \\ `y ∈ (sum c1 c2).env` by fs[SUBSET_DEF]
    \\ pop_assum mp_tac
    \\ simp_tac(srw_ss())[sum_def, EXISTS_PROD]
    \\ strip_tac \\ simp[Abbr`ff`, Abbr`f`]
    \\ rpt(qhdtm_x_assum`homotopic`mp_tac)
    \\ qpat_x_assum`w = _`(assume_tac o SYM) \\ fs[]
    \\ simp[homotopic_id_map_agent_id]
    \\ imp_res_tac compose_in_chu
    \\ simp[]
    \\ simp[restrict_def]
    \\ ntac 40 (pop_assum kall_tac)
    \\ ntac 5 strip_tac \\ simp[sum_eval_def]
    \\ PROVE_TAC[maps_to_in_chu, is_chu_morphism_def])
  \\ simp[CONJ_ASSOC]
  \\ conj_asm1_tac >- (
    drule compose_in_chu
    \\ disch_then drule \\ strip_tac
    \\ qpat_assum`k :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`j :- _ → _ -: _` o mp_then Any mp_tac)
    \\ strip_tac
    \\ simp[homotopic_id_map_agent_id]
    \\ simp[restrict_def, FUN_EQ_THM]
    \\ rpt(qhdtm_x_assum`homotopic`mp_tac)
    \\ simp[homotopic_id_map_agent_id]
    \\ qpat_assum`f2 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`g2 :- _ → _ -: _` o mp_then Any mp_tac)
    \\ strip_tac
    \\ qpat_assum`g2 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`f2 :- _ → _ -: _` o mp_then Any mp_tac)
    \\ strip_tac
    \\ qpat_assum`g1 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`f1 :- _ → _ -: _` o mp_then Any mp_tac)
    \\ strip_tac
    \\ qpat_assum`f1 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`g1 :- _ → _ -: _` o mp_then Any mp_tac)
    \\ strip_tac
    \\ simp[restrict_def]
    \\ ntac 4 strip_tac
    \\ simp[Abbr`d'`, mk_cf_def]
    \\ simp[Abbr`j`, Abbr`k`, mk_chu_morphism_def, restrict_def]
    \\ simp[sum_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD]
    \\ rw[] \\ simp[sum_eval_def]
    \\ TRY(qpat_x_assum`¬ _`mp_tac \\ simp[])
    \\ metis_tac[maps_to_in_chu, is_chu_morphism_def])
  \\ simp[is_subsum_def]
  \\ conj_tac >- simp[Abbr`d'`, sum_def]
  \\ conj_tac >- simp[Abbr`d'`, sum_def]
  \\ conj_tac
  >- (
    simp[Abbr`d'`, sum_def]
    \\ qpat_x_assum`d.env ⊆ _`mp_tac
    \\ simp[sum_def, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
    \\ rw[]
    \\ first_x_assum drule
    \\ rw[Abbr`ff`, Abbr`f`] \\ rw[]
    \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
  \\ conj_tac
  >- (
    simp[Abbr`d'`, mk_cf_def, restrict_def, FUN_EQ_THM]
    \\ `∀a x. (sum c1' c2').eval a x =
         if a ∈ (sum c1' c2').agent ∧ x ∈ (sum c1' c2').env
         then sum_eval c1'.eval c2'.eval a x
         else ARB` by rw[sum_def, mk_cf_def]
    \\ simp[]
    \\ rpt gen_tac
    \\ reverse IF_CASES_TAC \\ simp[]
    >- metis_tac[]
    \\ IF_CASES_TAC \\ simp[]
    \\ `F` suffices_by rw[]
    \\ pop_assum mp_tac
    \\ qpat_x_assum`d.env ⊆ _`mp_tac
    \\ simp[SUBSET_DEF]
    \\ fs[]
    \\ disch_then drule
    \\ simp_tac(srw_ss())[sum_def, Abbr`f`, Abbr`ff`, EXISTS_PROD]
    \\ rw[] \\ rw[]
    \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
  \\ qmatch_goalsub_abbrev_tac`c1' ≃ d1 -: w`
  \\ qmatch_goalsub_abbrev_tac`c2' ≃ d2 -: w`
  \\ `b1 ≃ d1 -: w ∧ b2 ≃ d2 -:w` suffices_by (
    `c1 ≃ c1' -:w ∧ c2 ≃ c2' -: w` by metis_tac[homotopy_equiv_def]
    \\ metis_tac[homotopy_equiv_trans, homotopy_equiv_sym] )
  \\ simp[homotopy_equiv_def]
  \\ simp[PULL_EXISTS]
  \\ qexists_tac`mk_chu_morphism b1 d1 <|
       map_agent := encode_sum o INL o g1.map.map_agent o OUTL o decode_sum;
       map_env := j.map.map_env |>`
  \\ qexists_tac`mk_chu_morphism d1 b1 <|
       map_agent := encode_sum o INL o f1.map.map_agent o OUTL o decode_sum;
       map_env := k.map.map_env |>`
  \\ qmatch_goalsub_abbrev_tac`homotopic _ (j1 o k1 -: _)`
  \\ qexists_tac`mk_chu_morphism b2 d2 <|
       map_agent := encode_sum o INR o g2.map.map_agent o OUTR o decode_sum;
       map_env := j.map.map_env |>`
  \\ qexists_tac`mk_chu_morphism d2 b2 <|
       map_agent := encode_sum o INR o f2.map.map_agent o OUTR o decode_sum;
       map_env := k.map.map_env |>`
  \\ qmatch_goalsub_abbrev_tac`homotopic _ (j2 o k2 -: _) (id b2 -: _)`
  \\ `b1 ∈ chu_objects w ∧ b2 ∈ chu_objects w`
  by metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ `d1 ∈ chu_objects w ∧ d2 ∈ chu_objects w`
  by (
    simp[Abbr`d1`, Abbr`d2`]
    \\ qpat_x_assum`d' ∈ _`mp_tac
    \\ qpat_x_assum`c1' ∈ _`mp_tac
    \\ qpat_x_assum`c2' ∈ _`mp_tac
    \\ simp[in_chu_objects]
    \\ simp[wf_def]
    \\ simp[finite_cf_def]
    \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ rw[] \\ gs[]
    \\ first_x_assum irule
    \\ rw[]
    \\ simp[Abbr`d'`,sum_def] )
  \\ simp[GSYM CONJ_ASSOC]
  \\ `b1.eval = λa. if a ∈ b1.agent then d.eval a else K ARB`
  by (
    simp[Abbr`b1`, mk_cf_def, restrict_def, FUN_EQ_THM]
    \\ rw[] \\ metis_tac[] )
  \\ `d1.eval = λa. if a ∈ d1.agent then d'.eval a else K ARB`
  by (
    simp[Abbr`d1`, mk_cf_def, restrict_def, FUN_EQ_THM]
    \\ rw[] >- metis_tac[]
    \\ qpat_x_assum`d' ∈ _`mp_tac
    \\ simp[chu_objects_def, wf_def]
    \\ metis_tac[])
  \\ qpat_x_assum`b1.eval = _`(assume_tac o SYM)
  \\ qpat_x_assum`d1.eval = _`(assume_tac o SYM)
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`k1`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac >- (
      simp[Abbr`d1`, Abbr`b1`]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- (
      simp[Abbr`d1`, Abbr`b1`, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ rpt gen_tac
    \\ strip_tac
    \\ qpat_x_assum`_ = d1.eval`(SUBST1_TAC o SYM)
    \\ simp[]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[Abbr`d1`]
      \\ fs[Abbr`b1`]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ pop_assum kall_tac
    \\ qpat_x_assum`_ = b1.eval`(SUBST1_TAC o SYM)
    \\ qpat_x_assum`a ∈ b1.agent` mp_tac
    \\ simp_tac(srw_ss())[]
    \\ simp_tac(srw_ss())[Abbr`b1`]
    \\ strip_tac
    \\ qpat_x_assum`a = _`SUBST_ALL_TAC
    \\ simp_tac(srw_ss())[]
    \\ qpat_x_assum`j :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_x_assum(qspecl_then[`encode_sum (INL x)`,`f'`]mp_tac)
    \\ impl_keep_tac >- (
      qpat_x_assum`f' ∈ _`mp_tac
      \\ simp_tac(srw_ss())[Abbr`d1`]
      \\ qpat_x_assum`d.agent = _`SUBST1_TAC
      \\ simp_tac(srw_ss())[sum_def]
      \\ rw[] )
    \\ disch_then SUBST1_TAC
    \\ simp[Abbr`j`, mk_chu_morphism_def, restrict_def]
    \\ metis_tac[] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`j1`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac >- (
      simp[Abbr`d1`, Abbr`b1`]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- (
      simp[Abbr`d1`, Abbr`b1`, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ rpt gen_tac
    \\ strip_tac
    \\ qpat_x_assum`_ = d1.eval`(SUBST1_TAC o SYM)
    \\ simp[]
    \\ qpat_x_assum`_ = b1.eval`(SUBST1_TAC o SYM)
    \\ simp_tac(srw_ss())[]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[Abbr`b1`]
      \\ qpat_x_assum`a ∈ _`mp_tac
      \\ simp[Abbr`d1`] \\ rw[] \\ rw[]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ pop_assum kall_tac
    \\ qpat_x_assum`a ∈ d1.agent` mp_tac
    \\ simp_tac(srw_ss())[Abbr`d1`]
    \\ strip_tac
    \\ qpat_x_assum`a = _`SUBST_ALL_TAC
    \\ simp_tac(srw_ss())[]
    \\ qpat_x_assum`k :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_x_assum(qspecl_then[`encode_sum (INL x)`,`f'`]mp_tac)
    \\ impl_keep_tac >- (
      qpat_x_assum`f' ∈ _`mp_tac
      \\ simp_tac(srw_ss())[Abbr`b1`]
      \\ simp_tac(srw_ss())[sum_def, Abbr`d'`]
      \\ rw[] )
    \\ disch_then SUBST1_TAC
    \\ simp[Abbr`k`, mk_chu_morphism_def, restrict_def])
  \\ `b2.eval = λa. if a ∈ b2.agent then d.eval a else K ARB`
  by (
    simp[Abbr`b2`, mk_cf_def, restrict_def, FUN_EQ_THM]
    \\ rw[] \\ metis_tac[] )
  \\ `d2.eval = λa. if a ∈ d2.agent then d'.eval a else K ARB`
  by (
    simp[Abbr`d2`, mk_cf_def, restrict_def, FUN_EQ_THM]
    \\ rw[] >- metis_tac[]
    \\ qpat_x_assum`d' ∈ _`mp_tac
    \\ simp[in_chu_objects, wf_def]
    \\ metis_tac[])
  \\ qpat_x_assum`b2.eval = _`(assume_tac o SYM)
  \\ qpat_x_assum`d2.eval = _`(assume_tac o SYM)
  \\ CONV_TAC(markerLib.move_conj_left(same_const``maps_to_in`` o #1 o strip_comb))
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`k2`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac >- (
      simp[Abbr`d2`, Abbr`b2`]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- (
      simp[Abbr`d2`, Abbr`b2`, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ rpt gen_tac
    \\ strip_tac
    \\ qpat_x_assum`_ = d2.eval`(SUBST1_TAC o SYM)
    \\ simp[]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[Abbr`d2`]
      \\ fs[Abbr`b2`]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ pop_assum kall_tac
    \\ qpat_x_assum`_ = b2.eval`(SUBST1_TAC o SYM)
    \\ qpat_x_assum`a ∈ b2.agent` mp_tac
    \\ simp_tac(srw_ss())[]
    \\ simp_tac(srw_ss())[Abbr`b2`]
    \\ strip_tac
    \\ qpat_x_assum`a = _`SUBST_ALL_TAC
    \\ simp_tac(srw_ss())[]
    \\ qpat_x_assum`j :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_x_assum(qspecl_then[`encode_sum (INR x)`,`f'`]mp_tac)
    \\ impl_keep_tac >- (
      qpat_x_assum`f' ∈ _`mp_tac
      \\ simp_tac(srw_ss())[Abbr`d2`]
      \\ qpat_x_assum`d.agent = _`SUBST1_TAC
      \\ simp_tac(srw_ss())[sum_def]
      \\ rw[] )
    \\ disch_then SUBST1_TAC
    \\ simp[Abbr`j`, mk_chu_morphism_def, restrict_def]
    \\ metis_tac[] )
  \\ CONV_TAC(markerLib.move_conj_left(same_const``maps_to_in`` o #1 o strip_comb))
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`j2`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac >- (
      simp[Abbr`d2`, Abbr`b2`]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- (
      simp[Abbr`d2`, Abbr`b2`, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ rpt gen_tac
    \\ strip_tac
    \\ qpat_x_assum`_ = d2.eval`(SUBST1_TAC o SYM)
    \\ simp[]
    \\ qpat_x_assum`_ = b2.eval`(SUBST1_TAC o SYM)
    \\ simp_tac(srw_ss())[]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[Abbr`b2`]
      \\ qpat_x_assum`a ∈ _`mp_tac
      \\ simp[Abbr`d2`] \\ rw[] \\ rw[]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ pop_assum kall_tac
    \\ qpat_x_assum`a ∈ d2.agent` mp_tac
    \\ simp_tac(srw_ss())[Abbr`d2`]
    \\ strip_tac
    \\ qpat_x_assum`a = _`SUBST_ALL_TAC
    \\ simp_tac(srw_ss())[]
    \\ qpat_x_assum`k :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_x_assum(qspecl_then[`encode_sum (INR x)`,`f'`]mp_tac)
    \\ impl_keep_tac >- (
      qpat_x_assum`f' ∈ _`mp_tac
      \\ simp_tac(srw_ss())[Abbr`b2`]
      \\ simp_tac(srw_ss())[sum_def, Abbr`d'`]
      \\ rw[] )
    \\ disch_then SUBST1_TAC
    \\ simp[Abbr`k`, mk_chu_morphism_def, restrict_def])
  \\ rpt(qhdtm_x_assum`homotopic`mp_tac)
  \\ simp[homotopic_id_map_agent_id]
  \\ qpat_assum`f2 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`g2 :- _ → _ -: _` o mp_then Any mp_tac) \\ strip_tac
  \\ qpat_assum`g2 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`f2 :- _ → _ -: _` o mp_then Any mp_tac) \\ strip_tac
  \\ qpat_assum`f1 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`g1 :- _ → _ -: _` o mp_then Any mp_tac) \\ strip_tac
  \\ qpat_assum`g1 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`f1 :- _ → _ -: _` o mp_then Any mp_tac) \\ strip_tac
  \\ qpat_assum`j2 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`k2 :- _ → _ -: _` o mp_then Any mp_tac) \\ strip_tac
  \\ qpat_assum`k2 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`j2 :- _ → _ -: _` o mp_then Any mp_tac) \\ strip_tac
  \\ qpat_assum`j1 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`k1 :- _ → _ -: _` o mp_then Any mp_tac) \\ strip_tac
  \\ qpat_assum`k1 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`j1 :- _ → _ -: _` o mp_then Any mp_tac) \\ strip_tac
  \\ simp[restrict_def]
  \\ ntac 4 strip_tac
  \\ conj_tac
  >- (
    simp[Abbr`j1`, Abbr`k1`, Abbr`b1`, Abbr`d1`,
         mk_chu_morphism_def, mk_cf_def,
         restrict_def, PULL_EXISTS]
    \\ rw[FUN_EQ_THM]
    \\ rw[sum_def, mk_cf_def, sum_eval_def, EXISTS_PROD] \\ rw[]
    \\ TRY (qpat_x_assum`¬ _`mp_tac) \\ simp[]
    \\ PROVE_TAC[maps_to_in_chu, is_chu_morphism_def])
  \\ conj_tac
  >- (
    qpat_x_assum`_ ⊆  _`mp_tac
    \\ simp[SUBSET_DEF, sum_def, PULL_EXISTS, EXISTS_PROD]
    \\ strip_tac
    \\ simp[Abbr`j1`, Abbr`k1`, Abbr`b1`, Abbr`d1`, Abbr`d'`,
            Abbr`ff`, Abbr`f`, mk_chu_morphism_def, mk_cf_def,
            restrict_def, PULL_EXISTS]
    \\ rw[FUN_EQ_THM]
    \\ rw[sum_def, mk_cf_def, sum_eval_def, EXISTS_PROD] \\ rw[]
    \\ TRY (first_assum drule \\ strip_tac)
    \\ TRY (qpat_x_assum`¬ _`mp_tac) \\ simp[]
    \\ PROVE_TAC[maps_to_in_chu, is_chu_morphism_def, PAIR_MAP_THM, decode_encode_pair])
  \\ conj_tac
  >- (
    simp[Abbr`j2`, Abbr`k2`, Abbr`b2`, Abbr`d2`,
         mk_chu_morphism_def, mk_cf_def,
         restrict_def, PULL_EXISTS]
    \\ rw[FUN_EQ_THM]
    \\ rw[sum_def, mk_cf_def, sum_eval_def, EXISTS_PROD] \\ rw[]
    \\ TRY (qpat_x_assum`¬ _`mp_tac) \\ simp[]
    \\ PROVE_TAC[maps_to_in_chu, is_chu_morphism_def])
  \\ qpat_x_assum`_ ⊆  _`mp_tac
  \\ simp[SUBSET_DEF, sum_def, PULL_EXISTS, EXISTS_PROD]
  \\ strip_tac
  \\ simp[Abbr`j2`, Abbr`k2`, Abbr`b2`, Abbr`d2`, Abbr`d'`,
          Abbr`ff`, Abbr`f`, mk_chu_morphism_def, mk_cf_def,
          restrict_def, PULL_EXISTS]
  \\ rw[FUN_EQ_THM]
  \\ rw[sum_def, mk_cf_def, sum_eval_def, EXISTS_PROD] \\ rw[]
  \\ TRY (first_assum drule \\ strip_tac)
  \\ TRY (qpat_x_assum`¬ _`mp_tac) \\ simp[]
  \\ PROVE_TAC[maps_to_in_chu, is_chu_morphism_def, PAIR_MAP_THM, decode_encode_pair]
QED

Theorem subtensor_homotopy_equiv:
  c1 ∈ chu_objects w ∧
  c2 ∈ chu_objects w ∧
  is_subtensor c1 c2 d ∧
  c1' ≃ c1 -: w ∧
  c2' ≃ c2 -: w
  ⇒
  ∃d'. d' ≃ d -: w ∧
    is_subtensor c1' c2' d'
Proof
  strip_tac
  \\ `d ∈ chu_objects w` by metis_tac[subtensor_in_chu_objects]
  \\ qpat_x_assum`is_subtensor _ _ _`mp_tac
  \\ simp[Once is_subtensor_def] \\ strip_tac
  \\ qmatch_assum_abbrev_tac`c1 ≃ b1 -: _`
  \\ qmatch_assum_abbrev_tac`c2 ≃ b2 -: _`
  \\ qpat_x_assum`c1' ≃ _ -: _`mp_tac
  \\ qpat_x_assum`c2' ≃ _ -: _`mp_tac
  \\ simp[Once homotopy_equiv_def]
  \\ disch_then(qx_choosel_then[`f2`,`g2`]strip_assume_tac)
  \\ simp[Once homotopy_equiv_def]
  \\ disch_then(qx_choosel_then[`f1`,`g1`]strip_assume_tac)
  \\ `c1' ∈ chu_objects w ∧ c2' ∈ chu_objects w` by fs[maps_to_in_chu]
  \\ `c1.world = w ∧ c2.world = w ∧ d.world = w ∧
      c1'.world = w ∧ c2'.world = w` by fs[in_chu_objects]
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ qabbrev_tac`f =
      λm. encode_morphism (
            swap_morphism (op_mor f2) o
            decode_morphism c1 (swap c2) m o
            f1 -: chu w -: chu w)`
  \\ `∀e. e ∈ (tensor c1 c2).env ⇒ f e ∈ (tensor c1' c2').env`
  by (
    simp[tensor_def, PULL_EXISTS, hom_def]
    \\ simp[Abbr`f`]
    \\ rpt strip_tac
    \\ qmatch_goalsub_abbrev_tac`encode_morphism m`
    \\ qexists_tac`m`
    \\ simp[Abbr`m`]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ irule maps_to_comp \\ simp[]
    \\ qexists_tac`swap c2`
    \\ conj_tac
    >- ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
    \\ simp[Once (GSYM swap_morphism_maps_to)] )
  \\ qexists_tac`mk_cf <|
       world := w;
       agent := (tensor c1' c2').agent;
       env := IMAGE f d.env;
       eval := (tensor c1' c2').eval |>`
  \\ qmatch_goalsub_abbrev_tac`d' ≃ d -: _`
  \\ simp[homotopy_equiv_def, PULL_EXISTS]
  \\ qexists_tac`mk_chu_morphism d' d <|
       map_agent := encode_pair o pair$## f1.map.map_agent f2.map.map_agent o decode_pair;
       map_env := f |>`
  \\ `SURJ f d.env d'.env`
  by (
    simp[SURJ_DEF, Abbr`f`, FORALL_PROD, EXISTS_PROD]
    \\ simp[Abbr`d'`, PULL_EXISTS]
    \\ metis_tac[] )
  \\ qexists_tac`mk_chu_morphism d d' <|
       map_agent := encode_pair o pair$## g1.map.map_agent g2.map.map_agent o decode_pair;
       map_env := λe'. @e. e ∈ d.env ∧ e' = f e
       |>`
  \\ qmatch_goalsub_abbrev_tac`homotopic _ (j o k -: _)`
  \\ simp[GSYM CONJ_ASSOC]
  \\ `d' ∈ chu_objects w`
  by (
    simp[in_chu_objects, Abbr`d'`]
    \\ conj_tac
    >- (
      qpat_x_assum`d.env ⊆ _`mp_tac
      \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
      \\ rpt strip_tac
      \\ first_x_assum drule \\ strip_tac
      \\ first_x_assum drule \\ strip_tac
      \\ `tensor c1' c2' ∈ chu_objects w` by simp[]
      \\ pop_assum mp_tac
      \\ simp_tac(srw_ss())[in_chu_objects, wf_def]
      \\ metis_tac[] )
    \\ simp[finite_cf_def]
    \\ `finite_cf d ∧ finite_cf (tensor c1' c2')`
    by ( fs[in_chu_objects] \\ metis_tac[wf_def, finite_tensor])
    \\ ntac 2 (pop_assum mp_tac)
    \\ simp[finite_cf_def] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`k`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d'`]
    \\ conj_tac
    >- (
      simp[tensor_def, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def])
    \\ simp[mk_cf_def]
    \\ rpt gen_tac
    \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ simp[Once tensor_def, EXISTS_PROD]
    \\ strip_tac \\ simp[]
    \\ qpat_x_assum`d.env ⊆ _`mp_tac
    \\ simp[SUBSET_DEF]
    \\ disch_then drule
    \\ strip_tac
    \\ `f f' ∈ (tensor c1' c2').env` by metis_tac[]
    \\ ntac 2 (pop_assum mp_tac)
    \\ simp_tac(srw_ss())[tensor_def, mk_cf_def, hom_def]
    \\ simp[] \\ ntac 2 strip_tac
    \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ reverse IF_CASES_TAC
    >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_x_assum`f f' = _`mp_tac
    \\ simp[Abbr`f`]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ disch_then(mp_tac o Q.AP_TERM`decode_morphism (c1':cf) (swap c2')`)
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ qspecl_then[`f2`,`c2'`,`c2`,`w`]mp_tac(Q.GENL[`f`,`a`,`b`,`w`]swap_morphism_maps_to)
    \\ simp[op_mor_swap_morphism] \\ strip_tac
    \\ conj_tac >- metis_tac[compose_in_chu]
    \\ disch_then(SUBST_ALL_TAC o SYM)
    \\ qpat_assum`f1 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then drule \\ strip_tac
    \\ drule compose_in_chu
    \\ disch_then drule \\ strip_tac
    \\ simp[restrict_def]
    \\ PROVE_TAC[maps_to_in_chu, is_chu_morphism_def, swap_components])
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`j`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac
    >- ( simp[Abbr`d'`, PULL_EXISTS] \\ metis_tac[] )
    \\ conj_tac
    >- (
      simp[Abbr`d'`, tensor_def, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ rpt gen_tac \\ strip_tac
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[SURJ_DEF]
    \\ gen_tac \\ strip_tac \\ simp[]
    \\ simp[Abbr`d'`, mk_cf_def]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac \\ simp[]
      \\ qpat_x_assum`a ∈ _`mp_tac
      \\ simp[tensor_def]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def, decode_encode_pair] )
    \\ pop_assum kall_tac
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ simp[Once tensor_def, EXISTS_PROD]
    \\ strip_tac \\ simp[]
    \\ simp[tensor_def, mk_cf_def, hom_def]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac \\ simp[]
      \\ qpat_x_assum`d.env ⊆ _`mp_tac
      \\ simp[SUBSET_DEF]
      \\ disch_then drule
      \\ simp[tensor_def, hom_def] )
    \\ pop_assum strip_assume_tac
    \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ simp[Abbr`f`]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ qspecl_then[`f2`,`c2'`,`c2`,`w`]mp_tac(Q.GENL[`f`,`a`,`b`,`w`]swap_morphism_maps_to)
    \\ simp[op_mor_swap_morphism] \\ strip_tac
    \\ conj_asm1_tac >- metis_tac[compose_in_chu]
    \\ reverse IF_CASES_TAC
    >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_assum`f1 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then drule \\ strip_tac
    \\ drule compose_in_chu
    \\ disch_then drule \\ strip_tac
    \\ simp[restrict_def]
    \\ reverse IF_CASES_TAC
    >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_assum`f1 :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`th)]))
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def, swap_components]
    \\ qpat_x_assum`homotopic _ (f1 o g1 -: _) _`mp_tac
    \\ simp[homotopic_id_map_agent_id]
    \\ qpat_assum`g1 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then (qpat_assum`f1 :- _ → _ -: _` o mp_then Any mp_tac)
    \\ strip_tac
    \\ simp[restrict_def]
    \\ qpat_x_assum`x' :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`th)]))
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_x_assum`homotopic _ (f2 o g2 -: _) _`mp_tac
    \\ simp[homotopic_id_map_agent_id]
    \\ qpat_assum`g2 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then (qpat_assum`f2 :- _ → _ -: _` o mp_then Any mp_tac)
    \\ strip_tac
    \\ simp[restrict_def])
  \\ `(λa e. if a ∈ d'.agent ∧ e ∈ d'.env then
            (tensor c1' c2').eval a e else ARB) = d'.eval`
  by ( simp[Abbr`d'`, mk_cf_def] )
  \\ conj_asm1_tac
  >- (
    simp[homotopic_id_map_agent_id]
    \\ qpat_assum`k :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then drule \\ strip_tac
    \\ simp[restrict_def]
    \\ qpat_assum`_ = d'.eval`(fn th => simp_tac std_ss [GSYM th])
    \\ simp[FUN_EQ_THM, PULL_FORALL]
    \\ rpt gen_tac \\ strip_tac
    \\ Cases_on`e ∈ d'.env` \\ simp[]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ simp[Abbr`j`, Abbr`k`, mk_chu_morphism_def, restrict_def]
    \\ `d'.agent = (tensor c1' c2').agent` by simp[Abbr`d'`]
    \\ `a ∈ (tensor c1' c2').agent` by metis_tac[]
    \\ pop_assum mp_tac
    \\ simp[Once tensor_def, EXISTS_PROD]
    \\ strip_tac \\ simp[]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[tensor_def]
      \\ metis_tac[is_chu_morphism_def, maps_to_in_chu] )
    \\ simp[tensor_def, mk_cf_def]
    \\ irule EQ_SYM
    \\ IF_CASES_TAC \\ simp[]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[tensor_def]
      \\ metis_tac[is_chu_morphism_def, maps_to_in_chu] )
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ simp[hom_def]
    \\ strip_tac
    \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ qpat_x_assum`homotopic _ (g1 o f1 -: _) _`mp_tac
    \\ simp[homotopic_id_map_agent_id]
    \\ qpat_assum`f1 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then (qpat_assum`g1 :- _ → _ -: _` o mp_then Any mp_tac)
    \\ strip_tac
    \\ simp[restrict_def]
    \\ qpat_x_assum`x :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`th)]))
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_x_assum`homotopic _ (g2 o f2 -: _) _`mp_tac
    \\ simp[homotopic_id_map_agent_id]
    \\ qpat_assum`f2 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then (qpat_assum`g2 :- _ → _ -: _` o mp_then Any mp_tac)
    \\ strip_tac
    \\ simp[restrict_def])
  \\ conj_asm1_tac
  >- (
    simp[homotopic_id_map_agent_id]
    \\ conj_tac
    >- ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ `j.dom = d` by metis_tac[maps_to_in_chu]
    \\ simp[pre_chu_def, restrict_def]
    \\ simp[FUN_EQ_THM, PULL_FORALL]
    \\ rpt gen_tac \\ strip_tac
    \\ Cases_on`e ∈ d.env` \\ simp[]
    \\ simp[Abbr`j`, Abbr`k`, mk_chu_morphism_def, restrict_def]
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ simp[Once tensor_def, EXISTS_PROD]
    \\ strip_tac \\ simp[]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[tensor_def, Abbr`d'`]
      \\ metis_tac[is_chu_morphism_def, maps_to_in_chu] )
    \\ simp[tensor_def, mk_cf_def]
    \\ irule EQ_SYM
    \\ IF_CASES_TAC \\ simp[]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[tensor_def]
      \\ metis_tac[is_chu_morphism_def, maps_to_in_chu] )
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ simp[hom_def]
    \\ strip_tac
    \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ qpat_x_assum`homotopic _ (f1 o g1 -: _) _`mp_tac
    \\ simp[homotopic_id_map_agent_id]
    \\ qpat_assum`g1 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then (qpat_assum`f1 :- _ → _ -: _` o mp_then Any mp_tac)
    \\ strip_tac
    \\ simp[restrict_def]
    \\ qpat_x_assum`x :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`th)]))
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_x_assum`homotopic _ (f2 o g2 -: _) _`mp_tac
    \\ simp[homotopic_id_map_agent_id]
    \\ qpat_assum`g2 :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then (qpat_assum`f2 :- _ → _ -: _` o mp_then Any mp_tac)
    \\ strip_tac
    \\ simp[restrict_def])
  \\ simp[is_subtensor_def]
  \\ conj_tac >- simp[Abbr`d'`, tensor_def]
  \\ conj_tac >- simp[Abbr`d'`]
  \\ conj_tac
  >- ( simp[Abbr`d'`, SUBSET_DEF] \\ metis_tac[SUBSET_DEF])
  \\ conj_tac
  >- (
    simp[Abbr`d'`, mk_cf_def, PULL_EXISTS, restrict_def]
    \\ rw[FUN_EQ_THM]
    \\ rw[]
    >- metis_tac[]
    \\ ntac 2 (pop_assum mp_tac)
    \\ simp[tensor_def, mk_cf_def]
    \\ metis_tac[] )
  \\ qmatch_goalsub_abbrev_tac`c1' ≃ d1 -: _`
  \\ qmatch_goalsub_abbrev_tac`c2' ≃ d2 -: _`
  \\ `b1 ≃ d1 -: w ∧ b2 ≃ d2 -:w` suffices_by (
    `c1 ≃ c1' -:w ∧ c2 ≃ c2' -: w` by metis_tac[homotopy_equiv_def]
    \\ metis_tac[homotopy_equiv_trans, homotopy_equiv_sym] )
  \\ `b1 ∈ chu_objects w ∧ b2 ∈ chu_objects w ∧
      d1 ∈ chu_objects w ∧ d2 ∈ chu_objects w`
  by (
    conj_tac >-metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ conj_tac >-metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ simp[Abbr`d1`, Abbr`d2`]
    \\ qpat_x_assum`d' ∈ _`mp_tac
    \\ qpat_x_assum`c1' ∈ _`mp_tac
    \\ qpat_x_assum`c2' ∈ _`mp_tac
    \\ simp[in_chu_objects]
    \\ simp[wf_def]
    \\ simp[finite_cf_def]
    \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ rw[] \\ gs[]
    \\ first_x_assum irule
    \\ rw[Abbr`d'`]
    \\ simp[tensor_def] )
  \\ simp[homotopy_equiv_def]
  \\ simp[PULL_EXISTS]
  \\ qexists_tac`mk_chu_morphism b1 d1 <|
       map_agent := g1.map.map_agent;
       map_env := encode_pair o pair$## f2.map.map_agent j.map.map_env o decode_pair |>`
  \\ qexists_tac`mk_chu_morphism d1 b1 <|
       map_agent := f1.map.map_agent;
       map_env := encode_pair o pair$## g2.map.map_agent k.map.map_env o decode_pair |>`
  \\ qmatch_goalsub_abbrev_tac`homotopic _ (j1 o k1 -: _)`
  \\ qexists_tac`mk_chu_morphism b2 d2 <|
       map_agent := g2.map.map_agent;
       map_env := encode_pair o pair$## f1.map.map_agent j.map.map_env o decode_pair |>`
  \\ qexists_tac`mk_chu_morphism d2 b2 <|
       map_agent := f2.map.map_agent;
       map_env := encode_pair o pair$## g1.map.map_agent k.map.map_env o decode_pair |>`
  \\ qmatch_goalsub_abbrev_tac`homotopic _ (j2 o k2 -: _) (id b2 -: _)`
  \\ simp[GSYM CONJ_ASSOC]
  (* TODO: use compose_in_chu to improve below here *)
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`k1`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac >- (
      simp[Abbr`d1`, Abbr`b1`, EXISTS_PROD, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- (
      simp[Abbr`d1`, Abbr`b1`, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ simp[Abbr`d1`, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
    \\ simp[Abbr`b1`, mk_cf_def, restrict_def]
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_x_assum`_ ∈ _.env`mp_tac
    \\ simp[Abbr`d'`, mk_cf_def] \\ strip_tac
    \\ simp[Abbr`j`, mk_chu_morphism_def, restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ gen_tac \\ strip_tac
    \\ irule EQ_SYM
    \\ simp[Once tensor_def]
    \\ `x' ∈ (tensor c1 c2).env` by metis_tac[SUBSET_DEF]
    \\ pop_assum mp_tac
    \\ simp[tensor_def, mk_cf_def]
    \\ simp[Abbr`f`, hom_def]
    \\ strip_tac \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ conj_asm1_tac
    >- (
      irule maps_to_comp \\ simp[]
      \\ qexists_tac`swap c2`
      \\ simp[Once CONJ_COMM]
      \\ simp[Once(GSYM(swap_morphism_maps_to))]
      \\ irule maps_to_comp \\ simp[]
      \\ metis_tac[] )
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ qmatch_goalsub_abbrev_tac`f2o o xf1 -: chu w`
    \\ `xf1 :- c1' → swap c2 -: chu w`
    by ( simp[Abbr`xf1`] \\ irule maps_to_comp \\ simp[] \\ metis_tac[])
    \\ `f2o :- swap c2 → swap c2' -: chu w`
    by (
      simp[Abbr`f2o`]
      \\ simp[Once (GSYM swap_morphism_maps_to)] )
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[pre_chu_def, restrict_def]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[Abbr`f2o`]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[Abbr`f2o`]
    \\ simp[Abbr`xf1`]
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[pre_chu_def, restrict_def]
    \\ reverse IF_CASES_TAC
    >- metis_tac[maps_to_in_chu, swap_components]
    \\ qpat_assum`g1 :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`(GSYM th))]))
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_x_assum`homotopic _ (f1 o g1 -: _) _`mp_tac
    \\ simp[homotopic_id_map_env_id] \\ strip_tac
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- ( simp[composable_in_def, pre_chu_def]
         \\ metis_tac[maps_to_in_chu] )
    \\ `f1.cod = c1` by metis_tac[maps_to_in_chu]
    \\ simp[pre_chu_def, restrict_def] \\ strip_tac
    \\ first_x_assum irule
    \\ metis_tac[maps_to_in_chu, is_chu_morphism_def])
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`j1`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac >- (
      simp[Abbr`d1`, Abbr`b1`, EXISTS_PROD, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- (
      simp[Abbr`d1`, Abbr`b1`, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ simp[Abbr`b1`, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
    \\ simp[Abbr`d1`, mk_cf_def, restrict_def]
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ simp[Abbr`d'`, mk_cf_def]
    \\ simp[Once tensor_def]
    \\ simp[Abbr`k`, mk_chu_morphism_def, restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ qmatch_assum_rename_tac`x ∈ d.env`
    \\ `x ∈ (tensor c1 c2).env` by metis_tac[SUBSET_DEF]
    \\ pop_assum mp_tac
    \\ simp[tensor_def, mk_cf_def]
    \\ simp[Abbr`f`, hom_def]
    \\ strip_tac \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ conj_asm1_tac
    >- (
      irule maps_to_comp \\ simp[]
      \\ qexists_tac`swap c2`
      \\ simp[Once CONJ_COMM]
      \\ simp[Once(GSYM(swap_morphism_maps_to))]
      \\ irule maps_to_comp \\ simp[]
      \\ metis_tac[] )
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ qmatch_goalsub_abbrev_tac`f2o o xf1 -: chu w`
    \\ `xf1 :- c1' → swap c2 -: chu w`
    by ( simp[Abbr`xf1`] \\ irule maps_to_comp \\ simp[] \\ metis_tac[])
    \\ `f2o :- swap c2 → swap c2' -: chu w`
    by (
      simp[Abbr`f2o`]
      \\ simp[Once (GSYM swap_morphism_maps_to)] )
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[pre_chu_def, restrict_def]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[Abbr`f2o`]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[Abbr`f2o`]
    \\ simp[Abbr`xf1`]
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[pre_chu_def, restrict_def]
    \\ pop_assum mp_tac \\ simp[] \\ strip_tac
    \\ reverse IF_CASES_TAC
    >- metis_tac[maps_to_in_chu, is_chu_morphism_def, swap_components]
    \\ qpat_assum`f1 :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`(th))]))
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_assum`x' :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`(th))]))
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_x_assum`homotopic _ (f2 o g2 -: _) _`mp_tac
    \\ simp[homotopic_id_map_agent_id] \\ strip_tac
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- ( simp[composable_in_def, pre_chu_def]
         \\ metis_tac[maps_to_in_chu] )
    \\ `g2.dom = c2` by metis_tac[maps_to_in_chu]
    \\ simp[pre_chu_def, restrict_def])
  \\ simp[Once homotopic_id_map_agent_id, GSYM CONJ_ASSOC]
  \\ conj_tac >- ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
  \\ conj_tac >- (
    qpat_x_assum`homotopic _ (f1 o g1 -: _) _`mp_tac
    \\ simp[homotopic_id_map_agent_id]
    \\ strip_tac
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp_tac(srw_ss())[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[pre_chu_def, restrict_def]
    \\ `k1.dom = b1 ∧ g1.dom = c1` by metis_tac[maps_to_in_chu]
    \\ simp[]
    \\ simp[Abbr`k1`, Abbr`j1`, mk_chu_morphism_def, restrict_def]
    \\ simp[Abbr`d1`]
    \\ strip_tac \\ gen_tac
    \\ reverse IF_CASES_TAC
    >- (simp[Abbr`b1`] \\ metis_tac[is_chu_morphism_def, maps_to_in_chu])
    \\ simp[Abbr`b1`, mk_cf_def, EXISTS_PROD, PULL_EXISTS, restrict_def, FUN_EQ_THM]
    \\ strip_tac \\ gen_tac
    \\ irule EQ_SYM
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum strip_assume_tac
    \\ simp[]
    \\ reverse IF_CASES_TAC >- metis_tac[is_chu_morphism_def, maps_to_in_chu]
    \\ simp[tensor_def, mk_cf_def] )
  \\ conj_tac >- (
    qpat_x_assum`homotopic _ (g1 o f1 -: _) _`mp_tac
    \\ simp[homotopic_id_map_agent_id]
    \\ strip_tac
    \\ conj_tac >- ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp_tac(srw_ss())[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[pre_chu_def, restrict_def]
    \\ `f1.dom = c1' ∧ j1.dom = d1` by metis_tac[maps_to_in_chu]
    \\ simp[]
    \\ simp[Abbr`k1`, Abbr`j1`, mk_chu_morphism_def, restrict_def]
    \\ simp[Abbr`b1`]
    \\ strip_tac \\ gen_tac
    \\ reverse IF_CASES_TAC
    >- (simp[Abbr`d1`] \\ metis_tac[is_chu_morphism_def, maps_to_in_chu])
    \\ simp[Abbr`d1`, mk_cf_def, EXISTS_PROD, PULL_EXISTS, restrict_def, FUN_EQ_THM]
    \\ strip_tac \\ gen_tac
    \\ irule EQ_SYM
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum strip_assume_tac
    \\ simp[]
    \\ reverse IF_CASES_TAC >- metis_tac[is_chu_morphism_def, maps_to_in_chu]
    \\ simp[Abbr`d'`, mk_cf_def]
    \\ simp[tensor_def, mk_cf_def] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`k2`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac >- (
      simp[Abbr`d2`, Abbr`b2`, EXISTS_PROD, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- (
      simp[Abbr`d2`, Abbr`b2`, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ simp[Abbr`d2`, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
    \\ simp[Abbr`b2`, mk_cf_def, restrict_def]
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_x_assum`_ ∈ _.env`mp_tac
    \\ simp[Abbr`d'`, mk_cf_def] \\ strip_tac
    \\ simp[Abbr`j`, mk_chu_morphism_def, restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ gen_tac \\ strip_tac
    \\ irule EQ_SYM
    \\ simp[Once tensor_def]
    \\ `x' ∈ (tensor c1 c2).env` by metis_tac[SUBSET_DEF]
    \\ pop_assum mp_tac
    \\ simp[tensor_def, mk_cf_def]
    \\ simp[Abbr`f`, hom_def]
    \\ strip_tac \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ conj_asm1_tac
    >- (
      irule maps_to_comp \\ simp[]
      \\ qexists_tac`swap c2`
      \\ simp[Once CONJ_COMM]
      \\ simp[Once(GSYM(swap_morphism_maps_to))]
      \\ irule maps_to_comp \\ simp[]
      \\ metis_tac[] )
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ qmatch_goalsub_abbrev_tac`f2o o xf1 -: chu w`
    \\ `xf1 :- c1' → swap c2 -: chu w`
    by ( simp[Abbr`xf1`] \\ irule maps_to_comp \\ simp[] \\ metis_tac[])
    \\ `f2o :- swap c2 → swap c2' -: chu w`
    by (
      simp[Abbr`f2o`]
      \\ simp[Once (GSYM swap_morphism_maps_to)] )
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[pre_chu_def, restrict_def]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[Abbr`f2o`]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[Abbr`f2o`]
    \\ simp[Abbr`xf1`]
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[pre_chu_def, restrict_def]
    \\ reverse IF_CASES_TAC
    >- metis_tac[maps_to_in_chu, swap_components, is_chu_morphism_def]
    \\ qpat_assum`f1 :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`(th))]))
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_assum`x'' :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`(th))]))
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_x_assum`homotopic _ (f2 o g2 -: _) _`mp_tac
    \\ simp[homotopic_id_map_agent_id] \\ strip_tac
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- ( simp[composable_in_def, pre_chu_def]
         \\ metis_tac[maps_to_in_chu] )
    \\ `g2.dom = c2` by metis_tac[maps_to_in_chu]
    \\ simp[pre_chu_def, restrict_def])
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[Abbr`j2`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac >- (
      simp[Abbr`d2`, Abbr`b2`, EXISTS_PROD, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- (
      simp[Abbr`d2`, Abbr`b2`, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ simp[Abbr`b2`, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
    \\ simp[Abbr`d2`, mk_cf_def, restrict_def]
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ simp[Abbr`d'`, mk_cf_def]
    \\ simp[Once tensor_def]
    \\ simp[Abbr`k`, mk_chu_morphism_def, restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ qmatch_assum_rename_tac`x ∈ d.env`
    \\ `x ∈ (tensor c1 c2).env` by metis_tac[SUBSET_DEF]
    \\ pop_assum mp_tac
    \\ simp[tensor_def, mk_cf_def]
    \\ simp[Abbr`f`, hom_def]
    \\ strip_tac \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ simp[]
    \\ conj_asm1_tac
    >- (
      irule maps_to_comp \\ simp[]
      \\ qexists_tac`swap c2`
      \\ simp[Once CONJ_COMM]
      \\ simp[Once(GSYM(swap_morphism_maps_to))]
      \\ irule maps_to_comp \\ simp[]
      \\ metis_tac[] )
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ qmatch_goalsub_abbrev_tac`f2o o xf1 -: chu w`
    \\ `xf1 :- c1' → swap c2 -: chu w`
    by ( simp[Abbr`xf1`] \\ irule maps_to_comp \\ simp[] \\ metis_tac[])
    \\ `f2o :- swap c2 → swap c2' -: chu w`
    by (
      simp[Abbr`f2o`]
      \\ simp[Once (GSYM swap_morphism_maps_to)] )
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[pre_chu_def, restrict_def]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[Abbr`f2o`]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[Abbr`f2o`]
    \\ simp[Abbr`xf1`]
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[pre_chu_def, restrict_def]
    \\ pop_assum mp_tac \\ simp[] \\ strip_tac
    \\ reverse IF_CASES_TAC
    >- metis_tac[maps_to_in_chu, is_chu_morphism_def, swap_components]
    \\ qpat_assum`g1 :- _ → _ -: _`mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`(GSYM th))]))
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_x_assum`homotopic _ (f1 o g1 -: _) _`mp_tac
    \\ simp[homotopic_id_map_env_id] \\ strip_tac
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- ( simp[composable_in_def, pre_chu_def]
         \\ metis_tac[maps_to_in_chu] )
    \\ `f1.cod = c1` by metis_tac[maps_to_in_chu]
    \\ simp[pre_chu_def, restrict_def]
    \\ disch_then irule
    \\ metis_tac[maps_to_in_chu, is_chu_morphism_def])
  \\ simp[Once homotopic_id_map_agent_id, GSYM CONJ_ASSOC]
  \\ conj_tac >- ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
  \\ conj_tac >- (
    qpat_x_assum`homotopic _ (f2 o g2 -: _) _`mp_tac
    \\ simp[homotopic_id_map_agent_id]
    \\ strip_tac
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      simp_tac(srw_ss())[composable_in_def, pre_chu_def]
      \\ metis_tac[maps_to_in_chu] )
    \\ simp[pre_chu_def, restrict_def]
    \\ `k2.dom = b2 ∧ f2.cod = c2` by metis_tac[maps_to_in_chu]
    \\ simp[]
    \\ simp[Abbr`k2`, Abbr`j2`, mk_chu_morphism_def, restrict_def]
    \\ simp[Abbr`d2`]
    \\ strip_tac \\ gen_tac
    \\ reverse IF_CASES_TAC
    >- (simp[Abbr`b2`] \\ metis_tac[is_chu_morphism_def, maps_to_in_chu])
    \\ simp[Abbr`b2`, mk_cf_def, EXISTS_PROD, PULL_EXISTS, restrict_def, FUN_EQ_THM]
    \\ strip_tac \\ gen_tac
    \\ irule EQ_SYM
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum strip_assume_tac
    \\ simp[]
    \\ reverse IF_CASES_TAC >- metis_tac[is_chu_morphism_def, maps_to_in_chu]
    \\ simp[tensor_def, mk_cf_def]
    \\ IF_CASES_TAC \\ simp[]
    \\ pop_assum mp_tac
    \\ simp[hom_def] \\ strip_tac
    \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ first_assum mp_tac
    \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
    \\ strip_tac
    \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`(th))]))
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ `g2.dom = c2` by metis_tac[maps_to_in_chu]
    \\ full_simp_tac std_ss [])
  \\ qpat_x_assum`homotopic _ (g2 o f2 -: _) _`mp_tac
  \\ simp[homotopic_id_map_agent_id]
  \\ strip_tac
  \\ conj_tac >- ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
  \\ conj_tac
  >- (
    simp_tac(srw_ss())[composable_in_def, pre_chu_def]
    \\ metis_tac[maps_to_in_chu] )
  \\ simp[pre_chu_def, restrict_def]
  \\ `f2.dom = c2' ∧ j2.dom = d2` by metis_tac[maps_to_in_chu]
  \\ simp[]
  \\ simp[Abbr`k2`, Abbr`j2`, mk_chu_morphism_def, restrict_def]
  \\ simp[Abbr`b2`]
  \\ strip_tac \\ gen_tac
  \\ reverse IF_CASES_TAC
  >- (simp[Abbr`d2`] \\ metis_tac[is_chu_morphism_def, maps_to_in_chu])
  \\ simp[Abbr`d2`, mk_cf_def, EXISTS_PROD, PULL_EXISTS, restrict_def, FUN_EQ_THM]
  \\ strip_tac \\ gen_tac
  \\ irule EQ_SYM
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ pop_assum strip_assume_tac
  \\ simp[]
  \\ reverse IF_CASES_TAC >- metis_tac[is_chu_morphism_def, maps_to_in_chu]
  \\ simp[Abbr`d'`, mk_cf_def]
  \\ simp[tensor_def, mk_cf_def]
  \\ IF_CASES_TAC \\ simp[]
  \\ IF_CASES_TAC \\ simp[]
  \\ pop_assum strip_assume_tac \\ simp[]
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
  \\ pop_assum mp_tac
  \\ simp[hom_def]
  \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
  \\ strip_tac
  \\ first_assum(fn th => CHANGED_TAC(DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`(th))]))
  \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
  \\ metis_tac[]
QED

val _ = export_theory();
